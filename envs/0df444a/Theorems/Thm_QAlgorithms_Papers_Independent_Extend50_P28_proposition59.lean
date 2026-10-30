-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_proposition59
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.proposition59
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:18:31.761991+00:00
-- url     : https://prove2.me/theorems/fd4321d4-9aa1-4047-af43-725441acaa5f
-- title:
--   Convexity and second derivative of inverse square root
-- statement:
--   Let $f(x)=x^{-1/2}=1/\sqrt x$ on the strictly positive real half-line. Then
--
--   $$
--   f\text{ is convex on }(0,\infty),\qquad f^{\prime\prime}(x)=\frac34x^{-5/2}\ge0\quad(x>0).
--   $$
--
--   This is the scalar convexity fact used on positive eigenvalues in (148)–(149).
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 26, Proposition 59

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.26, Proposition 59: corrected positive domain, convexity, exact
second derivative, and its nonnegative sign. See the inverseRoot discrepancy note. -/
theorem proposition59 :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) inverseRoot ∧
    ∀ x : ℝ, 0 < x →
      deriv (deriv inverseRoot) x = (3 / 4 : ℝ) * Real.rpow x (-5 / 2 : ℝ) ∧
      0 ≤ deriv (deriv inverseRoot) x := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
