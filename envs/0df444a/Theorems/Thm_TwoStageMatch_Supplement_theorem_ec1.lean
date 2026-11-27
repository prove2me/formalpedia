-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_theorem_ec1
-- name    : TwoStageMatch.Supplement.theorem_ec1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:14:33.170988+00:00
-- url     : https://prove2.me/theorems/7f124632-46bf-52dc-bb75-bb679b6f50db
-- title:
--   Theorem EC.1: optimal solutions of $\mathcal P^g$ do not depend on $g$
-- statement:
--   Let $\hat g,g:\mathbb R\to\mathbb R$ be two differentiable, monotone increasing and strictly convex functions, and consider an instance whose supply weights are all positive. If $x^*$ is an optimal solution of the balancing program
--   $$\min_x\ \sum_{j\in S}\frac1{w_j}\,\hat g\Big(w_j\big(1-\sum_{i\in N(j)}x_{ij}\big)\Big)\quad\text{over fractional matchings }x\text{ of }G[D_1,S],$$
--   then $x^*$ is also an optimal solution of the same program with $g$ in place of $\hat g$.
--
--   So the first-stage marginals of Algorithm 1 do not depend on the choice of $g$ (Remark 1); $g$ may be chosen for computational convenience.
--
--   Differences from the source:
--   - encoding: weights w_j ≥ 0 (p.9) → w_j > 0 for every j; reason: 𝒫^g divides by w_j and is undefined when some w_j = 0
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Theorem EC.1, p.ec8; proof pp.ec8–ec9

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

namespace TwoStageMatch.Supplement

/-- **Theorem EC.1** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.ec8; proof pp.ec8–ec9). Fix
two arbitrary differentiable, monotone increasing and strictly convex functions `ĝ(·)` and `g(·)`.
If `{x*_{ij}}` is an optimal solution in the convex program `𝒫^g` with function `ĝ(·)`,
`{x*_{ij}}` is also an optimal solution in the convex program `𝒫^g` with function `g(·)`.

Stated on every instance whose supply weights are all positive.

**Formalization Note.** `𝒫^g` and its optimal solutions are the published
`TwoStageMatch.objective` / `IsOptimal`. The program divides by `w_j`, so the instance has
`w_j > 0` for all `j`. -/
theorem theorem_ec1 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S)
    (hw : ∀ j, 0 < I.w j) (ĝ g : ℝ → ℝ)
    (hĝd : Differentiable ℝ ĝ) (hĝm : Monotone ĝ) (hĝc : StrictConvexOn ℝ Set.univ ĝ)
    (hgd : Differentiable ℝ g) (hgm : Monotone g) (hgc : StrictConvexOn ℝ Set.univ g)
    (x : D₁ → S → ℝ) (hx : IsOptimal I ĝ x) : IsOptimal I g x := by sorry

end TwoStageMatch.Supplement
