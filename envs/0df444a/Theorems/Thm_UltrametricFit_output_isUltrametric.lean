-- Prove2me | Theorems.Thm_UltrametricFit_output_isUltrametric
-- name    : UltrametricFit.output_isUltrametric
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:43.825545+00:00
-- url     : https://prove2.me/theorems/4e15c5e1-f590-4d1e-849b-213e1e604171
-- title:
--   §3, p.8 — a run exists, and its output is a well-defined ultrametric
-- statement:
--   Let $X$ be an instance, $x$ a feasible point of the LP and $\delta\in(0,1/2)$. A run of Merge($\delta$) on $x$ exists. For each run, all species lie in one cluster at the end of layer $L$ (for $n\ge1$), an output exists and is unique on pairs, and it is an ultrametric with
--   $$U(i,j)\in\{D_1,\dots,D_L\}\qquad\text{for all }i\ne j.$$
--   So the output of the algorithm is a feasible solution of the fitting problem, whatever merge order the run uses.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of the LP (§3) → $x$ any feasible point; reason: optimal solutions are feasible, so the page's case is included
--   - encoding: Algorithm 1 with unspecified merge order → a relation `IsRun` with a universal quantifier over runs, and a relational output `IsOutput`; reason: the paper fixes no order (and §5 speaks of the worst one), so every order is an execution of the algorithm
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
--   - generalization: the page argues that $U$ is well defined and an ultrametric, and that each layer's loop ends implicitly → also: a run exists, and the output is unique on pairs; reason: these make the conclusion non-vacuous and follow from the same observations; dropping them gives the page's claim
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §3, p.8

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun

namespace UltrametricFit

/-- **The run and its output are well defined, and the output is an ultrametric**, Charikar, Gao,
STOC 2027 submission (manuscript sha256 87af12a2…), §3, p.8. For every feasible `x`: a run exists
(each while-loop terminates, as the family of clusters shrinks); and for every run, all species are
in one cluster at the end of layer `L`, an output exists, it is unique on pairs, and it is an
ultrametric with values in `{D_1, …, D_L}`.

**Formalization Note.** §3 speaks of an optimal solution, and the argument uses only feasibility.
`C (numLayers X) = {univ}` is stated for `n ≥ 1`; at `n = 0` there are no clusters. -/
theorem output_isUltrametric {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (x : ℕ → Fin n → Fin n → ℝ) (hx : IsFeasible X x) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (∃ C M, IsRun X x δ C M) ∧
    ∀ C M, IsRun X x δ C M →
      (0 < n → C (numLayers X) = {Finset.univ}) ∧
      (∃ U, IsOutput X C U) ∧
      ∀ U, IsOutput X C U →
        IsUltrametric U ∧
        (∀ i j, i ≠ j → ∃ ℓ ∈ Finset.Icc 1 (numLayers X), U i j = layerValue X ℓ) ∧
        ∀ U', IsOutput X C U' → ∀ i j, i ≠ j → U' i j = U i j := by sorry

end UltrametricFit
