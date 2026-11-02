-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_profile_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.profile_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:00:04.964195+00:00
-- url     : https://prove2.me/theorems/be45c34f-0fcf-4a34-bc21-50a3d408f85c
-- title:
--   Monotonicity and positive interior derivative of the raw profiles
-- statement:
--   Fix an integer $d\ge2$. Let $q_d$ be the minimum constrained Schmidt tangle at overlap $F$, and let $c_d=\sqrt{q_d}$. Both functions are nondecreasing on $[1/d,1]$, and $q_d(1/d)=c_d(1/d)=0$. For every $F\in(1/d,1)$, with $\gamma_d(F)=\sqrt{F/d}+\sqrt{(d-1)(1-F)/d}$ and $\delta_d(F)=\sqrt{F/d}-\sqrt{(1-F)/(d(d-1))}$,
--
--   $$
--   q_d'(F)=4\sqrt{d/F}\,\gamma_d(F)\delta_d(F)\bigl(\gamma_d(F)+\delta_d(F)\bigr)>0.
--   $$
--
--   The derivative assertion is restricted to the interior; it does not apply a total two-sided derivative to a singular endpoint formula.
--
--   This monotonicity is the profile property used to simplify the arbitrary-state fidelity bound.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 10, §3.3, (3.35): monotonicity of the raw profiles

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9--10, (3.35): both raw profiles are monotone on the closed domain;
the displayed positive derivative is asserted only in its open interior. -/
theorem profile_monotonicity (d : ℕ) (hd : 2 ≤ d) :
    MonotoneOn (constrainedSchmidtTangle d) (Set.Icc (1 / (d : ℝ)) 1) ∧
    MonotoneOn (rawC d) (Set.Icc (1 / (d : ℝ)) 1) ∧
    constrainedSchmidtTangle d (1 / (d : ℝ)) = 0 ∧ rawC d (1 / (d : ℝ)) = 0 ∧
    ∀ F ∈ Set.Ioo (1 / (d : ℝ)) 1,
      HasDerivAt (constrainedSchmidtTangle d)
        (4 * Real.sqrt ((d : ℝ) / F) * minimizingLargeAmplitude d F * minimizingSmallAmplitude d F *
          (minimizingLargeAmplitude d F + minimizingSmallAmplitude d F)) F ∧
      0 < 4 * Real.sqrt ((d : ℝ) / F) * minimizingLargeAmplitude d F * minimizingSmallAmplitude d F *
        (minimizingLargeAmplitude d F + minimizingSmallAmplitude d F) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
