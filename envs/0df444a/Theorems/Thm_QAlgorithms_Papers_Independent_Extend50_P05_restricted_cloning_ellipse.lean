-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_restricted_cloning_ellipse
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.restricted_cloning_ellipse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:21:40.458861+00:00
-- url     : https://prove2.me/theorems/9f5b6fdc-34bc-4e24-b6ad-34b5989e8f2b
-- title:
--   Exact restricted cloning ellipse
-- statement:
--   Let $d\ge2$. Restrict the input-first Choi matrix of a CPTP $1\to2$ channel to the four rank-$d$ partially transposed permutations, with no identity or output-swap term. The shrink pair $(p,q)$ of its two depolarizing marginals is attainable exactly when both coordinates lie in $[-1/(d^2-1),1]$ and
--
--   $$
--   \left(\frac{p+q-1}{2}\right)^2\le\frac{(1-p)(1-q)}{d^2}.
--   $$
--
--   Equivalently, with $s=p+q$, $t=p-q$, $a=(d^2-1)^{-1/2}$, $b=(d^2-1)^{-1}$ and $c_d=(d^2-2)/(d^2-1)$, the criterion is $t^2/a^2+(s-c_d)^2/b^2\le d^2$.
--
--   This is the entire restricted feasible region, including negative parameters and interior points.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 10, Theorem 5: exact restricted cloning ellipse

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.10, Theorem 5: necessity and attainment for exactly the restricted family.
The printed interval for the pair is read coordinatewise, as the proof requires. -/
theorem restricted_cloning_ellipse (d : ℕ) (hd : 2 ≤ d) (p q : ℝ) :
    (RestrictedAchievable d p q ↔
      (-(1 : ℝ) / ((d : ℝ) ^ 2 - 1) ≤ p ∧ p ≤ 1) ∧
      (-(1 : ℝ) / ((d : ℝ) ^ 2 - 1) ≤ q ∧ q ≤ 1) ∧
      ((p + q - 1) / 2) ^ 2 ≤ (1 - p) * (1 - q) / (d : ℝ) ^ 2) ∧
    (RestrictedAchievable d p q ↔ InEllipse d (d : ℝ) (p + q) (p - q)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
