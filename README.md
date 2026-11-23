# ZhiyouFormal — Lean 4 Machine-Checked Formalization of the Xiong Wei Unified Trilogy

[![Lean 4](https://img.shields.io/badge/Lean-4.14.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.14.0-green)](https://github.com/leanprover-community/mathlib4)
[![sorry](https://img.shields.io/badge/sorry-0-brightgreen)]()
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24456674.svg)](https://doi.org/10.5281/zenodo.24456674)
[![Zenodo (direct upload)](https://zenodo.org/badge/DOI/10.5281/zenodo.24454857.svg)](https://doi.org/10.5281/zenodo.24454857)

**48 machine-checked theorems · 4 model-consistency constructions · 0 `sorry` · 4 transparently declared external axioms**

This repository is the complete Lean 4 + Mathlib4 formal verification package accompanying the
three-volume *Xiong Wei Unified Trilogy* (熊巍三部曲):

| Vol. | Work | Chinese preprint | English preprint |
|---|---|---|---|
| 1 | **Continuous Ontology** (连续本体论) | [10.5281/zenodo.20162911](https://doi.org/10.5281/zenodo.20162911) | [10.5281/zenodo.24453152](https://doi.org/10.5281/zenodo.24453152) |
| 2 | **Probability Cloud Evolution Theory** (概率云演化论) | [10.5281/zenodo.24454840](https://doi.org/10.5281/zenodo.24454840) | [10.5281/zenodo.24454846](https://doi.org/10.5281/zenodo.24454846) |
| 3 | **Zhiyou Unified Theory** (秩由统一理论) | [10.5281/zenodo.24454849](https://doi.org/10.5281/zenodo.24454849) | [10.5281/zenodo.24454855](https://doi.org/10.5281/zenodo.24454855) |

Software archive (this repository, auto-archived per release): **[10.5281/zenodo.24456674](https://doi.org/10.5281/zenodo.24456674)** — concept DOI, always resolves to the latest archived release.
Snapshot of v1.0.0 uploaded directly to Zenodo: [10.5281/zenodo.24454857](https://doi.org/10.5281/zenodo.24454857).

> **The point of this repository.** A 10,000-word ontological essay is not evidence. A `git clone`
> plus a Lean kernel run that prints *no goals* is. Everything below is reproducible on a clean
> machine in three commands.

---

## 1. Quick start (clean machine)

```bash
# prerequisites: elan (auto-installed by the VS Code Lean4 extension) + git
git clone https://github.com/tenabuy-bot/ZhiyouFormal.git
cd ZhiyouFormal

# Lean toolchain is pinned by lean-toolchain → leanprover/lean4:v4.14.0
lake update          # resolves Mathlib v4.14.0 + 8 dependencies
lake exe cache get   # downloads prebuilt Mathlib oleans (≈3–4 GB, one-off)
lake build           # builds all 5 modules + AxiomAudit
```

Expected tail of the build:

```text
Build completed successfully.
```

Any `declaration uses 'sorry'` warning, or any red goal in the VS Code Lean Infoview, means the
claim is not verified. There should be none.

### Windows quick verify (no full Mathlib rebuild)

If you already have Mathlib oleans cached, `verify.ps1` type-checks every module directly with the
Lean kernel and reuses the cache:

```powershell
pwsh ./verify.ps1          # checks 5 modules (~a few minutes)
pwsh ./verify.ps1 -Audit   # + axiom audit (asserts sorryAx = 0)
```

---

## 2. Module map and theorem index

```text
ZhiyouFormal.lean                       root import module
ZhiyouFormal/
├── Book1_ContinuousOntology.lean       Vol. 1 — axiomatic model + 16 physics/topology theorems
├── Book2_ProbabilityCloud.lean         Vol. 2 — 5 axioms + 10 probability/emergence/convergence theorems
├── Book3_ZhiyouTheory.lean             Vol. 3 — layer-0 kernel + 17 dynamics/niche/Manski theorems
├── CrossDiscipline_Correspondence.lean cross-disciplinary downward-compatibility lemmas (5)
└── AxiomAudit.lean                     `#print axioms` audit for every theorem
```

Selected results (module → theorem):

**Book 1 — Continuous Ontology**
- `B1_T4_decoherence_phase_average_zero` — uniform random phase ⇒ 〈cos φ〉 = 0 (statistical decoherence).
- `B1_T5_unimodular_uniform_background_immunity` — a uniform ground state exerts no gravitational pull.
- `B1_T5_unimodular_cosmological_constant_integration` — Λ emerges as an integration constant (unimodular gravity).
- `B1_T6_bec_equivalence_principle_bounds` — BEC equivalence-principle deviation bound, compatible with MICROSCOPE.
- `B1_T9_least_potential_locks_X844_Dic3` — moduli ordering 52 < 72 < 102 uniquely locks three generations.
- `B1_T12_tracker_dark_energy_w0` — Ratra–Peebles w₀ = −10/11 at α = 1/5.
- `B1_T14_pure_dephasing_diagonal_freeze_counterexample` — pure dephasing freezes the diagonal (Born rule is indispensable).

**Book 2 — Probability Cloud Evolution Theory**
- `B2_T1_projection_idempotent_and_variance_contraction` — projective collapse is idempotent and strictly contracts variance.
- `B2_T6_causal_do_neq_observation` — P(Y|X) = 0.9 ≠ P(Y|do(X)) = 0.5 under a confounder (the LLM "correlation ceiling").
- `B2_T10_general_to_special_zhiyou_convergence` — σ² → 0 limit recovers dR/dt = Q − D exactly.
- `B2_T11_chaos_reserve_prevents_rigidity_trap` — 10 % chaos reserve prevents order-trap lock-in.

**Book 3 — Zhiyou Unified Theory**
- `B3_T1_zhiyou_non_conservation` — explicit constructions falsify conservation of "rank surplus".
- `B3_T12_target_overlap_inverted_U_optimum` — unique optimum α\* = A/(2B).
- `B3_T17_three_price_identity` and `B3_T17_manski_partial_non_identification` — three-price identity and Manski partial identification, both constructed explicitly.

**Cross-discipline**
- DCF (finance), six-dimensional buyer cost (economics), Hobbes' social contract (political science),
  Durkheim anomie (sociology) and order-trap (management) are derived as boundary cases.

---

## 3. What "0 sorry" does and does not mean

`0 sorry` means: **no proof is left as a placeholder**. It does **not** mean the physical universe
has been proved to obey these axioms. As in any formalization, the content of the theorems is
exactly the mathematical consequence of the axioms, and four external axioms are declared
openly in `AxiomAudit.lean` (physical/analytic inputs that are not derivable from Lean's core).
`#print axioms` output is archived in [`Verification/axiom_audit.txt`](Verification/axiom_audit.txt).

Read it as: *if you accept the four declared axioms, then every one of the 48 theorems follows by
machine-checked proof.* That is a falsifiable, auditable standard — and it is the reason this
repository exists.

---

## 4. Hardware and dependency notes

| Item | Value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.14.0` (pinned in `lean-toolchain`) |
| Mathlib | `v4.14.0` |
| Dependencies | batteries, aesop, Qq, Cli, plausible, LeanSearchClient, importGraph, proofwidgets |
| Disk (with Mathlib cache) | ≈ 4–6 GB |
| RAM for `lake build` | ≥ 8 GB (Mathlib oleans cached; ~16 GB recommended) |

The local authoring machine was offline from GitHub, so its `lake-manifest.json` used path locks;
that file is intentionally **not** shipped here. `lake update` regenerates a clean git manifest.

---

## 5. Citation

```bibtex
@software{xiong2026zhiyouformal,
  author       = {Xiong, Wei},
  title        = {ZhiyouFormal: Lean 4 Machine-Checked Formalization of the Xiong Wei Unified Trilogy},
  year         = {2026},
  version      = {1.0.0},
  doi          = {10.5281/zenodo.24454857},
  url          = {https://doi.org/10.5281/zenodo.24454857}
}
```

See [`CITATION.cff`](CITATION.cff). Repository is MIT-licensed; the archived release is
MIT-licensed on Zenodo as well.

## 6. Acknowledgements

Lean 4 and Mathlib are the work of the Lean FRO and the Mathlib community. This repository only
formalizes the trilogy's models and results; it stands entirely on their toolchain.
