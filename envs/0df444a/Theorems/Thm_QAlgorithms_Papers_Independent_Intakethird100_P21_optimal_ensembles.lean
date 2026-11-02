-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_optimal_ensembles
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.optimal_ensembles
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:03:50.362537+00:00
-- url     : https://prove2.me/theorems/c32f1138-215d-4cf7-9f85-45e62706f247
-- title:
--   Structure and weights of attaining isotropic decompositions
-- statement:
--   Let $d\ge3$, $F\in[0,1]$, $a=4(d-1)/d^2$, $t=2(2d-3)/(d(d-1))$, and $M=2(d-1)/d$. For the isotropic density $\rho_{d,F}$, an attaining finite normalized tangle ensemble exists whose positive-weight pure states all have tangle $\tau(\rho_{d,F})$ when $F\le a$, and have tangles in $\{t,M\}$ when $F>a$. In the latter case the total weights of these two tangle classes are respectively
--
--   $$
--   w_t=\frac{1-F}{1-a},\qquad w_M=\frac{F-a}{1-a}.
--   $$
--
--   There is also an attaining concurrence ensemble using only normalized product states or maximally entangled states at positive weights. Its total maximally entangled weight is
--
--   $$
--   w_{\max}=\begin{cases}0&F\le1/d,\\(dF-1)/(d-1)&F>1/d.\end{cases}
--   $$
--
--   Zero-weight members impose no type restriction. At $F=1$ only maximal entanglement need have positive weight; below the separability threshold common tangle is zero.
--
--   These are existence statements about constructed optimizers, rather than claims about every optimal ensemble.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 13, §3.4.3: structure of optimal isotropic decompositions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.13: existence of attaining isotropic decompositions with common
tangle below the breakpoint, two allowed tangle values above, and product/maximal
concurrence components. No universal classification of optimal ensembles is claimed. -/
theorem optimal_ensembles (d : ℕ) (hd : 3 ≤ d) (F : ℝ) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    (∃ e : PureEnsemble (Fin d × Fin d), IsOptimalPureEnsemble pureTangle (isotropicDensityAtFidelity d F) e ∧
      (∀ k, 0 < e.weight k →
        if F ≤ tangentPoint d then pureTangle (e.vector k) = tangle (isotropicDensityAtFidelity d F)
        else pureTangle (e.vector k) = 2*(2*(d : ℝ)-3)/((d : ℝ)*((d : ℝ)-1)) ∨
          pureTangle (e.vector k) = 2*((d : ℝ)-1)/d) ∧
      (tangentPoint d < F →
        (∑ k, if pureTangle (e.vector k) = 2*(2*(d : ℝ)-3)/((d : ℝ)*((d : ℝ)-1))
          then e.weight k else 0) = (1-F)/(1-tangentPoint d) ∧
        (∑ k, if pureTangle (e.vector k) = 2*((d : ℝ)-1)/d then e.weight k else 0) =
          (F-tangentPoint d)/(1-tangentPoint d))) ∧
    (∃ e : PureEnsemble (Fin d × Fin d), IsOptimalPureEnsemble pureConcurrence (isotropicDensityAtFidelity d F) e ∧
      (∀ k, 0 < e.weight k → IsPureProductState (e.vector k) ∨ IsMaximallyEntangled (e.vector k)) ∧
      (∑ k, if IsMaximallyEntangled (e.vector k) then e.weight k else 0) =
        (if F ≤ 1/(d : ℝ) then 0 else ((d : ℝ)*F-1)/((d : ℝ)-1))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
