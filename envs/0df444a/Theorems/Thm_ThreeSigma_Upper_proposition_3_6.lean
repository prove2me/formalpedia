-- Prove2me | Theorems.Thm_ThreeSigma_Upper_proposition_3_6
-- name    : ThreeSigma.Upper.proposition_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:59.285825+00:00
-- url     : https://prove2.me/theorems/f6f018c0-8f4f-48a5-ae3e-219ccd353130
-- title:
--   Proposition 3.6 — a point with residual at most four
-- statement:
--   Let $n>4$, let $d$ be any natural number, and let $A\in[-1,1]^{d\times n}$. Put $\Delta=\sqrt{3n\operatorname{arsinh}(10d/n)}$ and
--   $$\mathcal K=\{z\in[-1,1]^n: |(Az)_i|\le\Delta\text{ for every row }i\}.$$
--   Then
--   $$\exists z\in\mathcal K,\qquad n-\|z\|_2^2\le4.$$
--   This is the fractional-point existence result used for the final signing bound. No potential-minimizer existence or scalar estimate is assumed.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with coordinates indexed 1 through n → EuclideanSpace ℝ (Fin n) with coordinates indexed 0 through n−1; reason: canonical isometric coordinate representation; no instances are excluded
--   - encoding: constraints for all 2d original and negated rows → absolute-value constraints for the d original rows; reason: each pair of one-sided inequalities is equivalent to one absolute-value inequality, including d=0
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Proposition 3.6, p. 8, with (1)–(2), p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Geometry

namespace ThreeSigma.Upper

/-- Proposition 3.6, with (1)-(2) constructed from the input matrix. -/
theorem proposition_3_6 {n d : ℕ} (hn : 4 < n) (A : Fin d → Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ z : E n, z ∈ K A ∧ R z ≤ 4 := by sorry

end ThreeSigma.Upper
