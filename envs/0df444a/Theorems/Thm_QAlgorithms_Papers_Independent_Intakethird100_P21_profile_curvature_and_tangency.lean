-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_profile_curvature_and_tangency
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.profile_curvature_and_tangency
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:02:35.107053+00:00
-- url     : https://prove2.me/theorems/86958fed-ceda-4005-b7cc-529dbbef1a3e
-- title:
--   A single inflection and the unique supporting tangent
-- statement:
--   Let $d\ge3$ and let $q_d(F)=2(1-\gamma_d(F)^4-(d-1)\delta_d(F)^4)$ on $[1/d,1]$, with $\gamma_d(F)=\sqrt{F/d}+\sqrt{(d-1)(1-F)/d}$ and $\delta_d(F)=\sqrt{F/d}-\sqrt{(1-F)/(d(d-1))}$. This profile is twice differentiable in the interior and has a unique inflection point $r\in(1/d,1)$: $q_d''$ is positive below $r$, zero at $r$, and negative above $r$. The function $c_d=\sqrt{q_d}$ is concave on the closed interval. The equation
--
--   $$
--   q_d'(a)=\frac{2(d-1)/d-q_d(a)}{1-a},\qquad a\in(1/d,1),
--   $$
--
--   has the unique solution $a_d=4(d-1)/d^2$, with
--
--   $$
--   q_d(a_d)=\frac{2(2d-3)}{d(d-1)},\qquad q_d'(a_d)=\frac{2d}{d-1}.
--   $$
--
--   The line $q_d(a_d)+q_d'(a_d)(F-a_d)$ lies below $q_d(F)$ throughout $[1/d,1]$.
--
--   These properties identify the straight segment needed in the isotropic tangle convex envelope. The endpoint $a=1$ and the exceptional dimension $d=2$ are excluded from the tangency and inflection claims.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 13, §3.4.3, (3.40) and tangent calculation: curvature and unique supporting tangent

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.12--13, (3.40) and tangent calculation: one interior inflection,
unique supporting tangent before F=1, and closed-domain concavity of c_d.
The restriction d>=3 excludes q_2''=8. -/
theorem profile_curvature_and_tangency (d : ℕ) (hd : 3 ≤ d) :
    (∀ x ∈ Set.Ioo (1 / (d : ℝ)) 1,
      DifferentiableAt ℝ (explicitQ d) x ∧ DifferentiableAt ℝ (deriv (explicitQ d)) x) ∧
    (∃ b ∈ Set.Ioo (1 / (d : ℝ)) 1,
      deriv (deriv (explicitQ d)) b = 0 ∧
      (∀ x ∈ Set.Ioo (1 / (d : ℝ)) b, 0 < deriv (deriv (explicitQ d)) x) ∧
      (∀ x ∈ Set.Ioo b 1, deriv (deriv (explicitQ d)) x < 0)) ∧
    ConcaveOn ℝ (Set.Icc (1 / (d : ℝ)) 1) (rawC d) ∧
    explicitQ d (tangentPoint d) = 2 * (2*(d : ℝ)-3) / ((d : ℝ)*((d : ℝ)-1)) ∧
    deriv (explicitQ d) (tangentPoint d) = 2*d / ((d : ℝ)-1) ∧
    (∀ x ∈ Set.Ioo (1 / (d : ℝ)) 1,
      (deriv (explicitQ d) x =
        (2*((d : ℝ)-1)/d - explicitQ d x) / (1-x) ↔ x = tangentPoint d)) ∧
    (∀ F ∈ Set.Icc (1 / (d : ℝ)) 1,
      explicitQ d (tangentPoint d) + (2*d/((d : ℝ)-1))*(F-tangentPoint d) ≤
        explicitQ d F) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
