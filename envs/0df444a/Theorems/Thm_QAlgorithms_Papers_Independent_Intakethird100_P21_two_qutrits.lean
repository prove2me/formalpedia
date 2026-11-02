-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_two_qutrits
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.two_qutrits
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:01:48.929027+00:00
-- url     : https://prove2.me/theorems/7c75a462-830c-41a5-8da3-2598d115ff85
-- title:
--   Two-qutrit formulas, tangent point and optimal component types
-- statement:
--   For two qutrits and $F\in[0,1]$, let $\rho_{3,F}=FP_3+(1-F)(I-P_3)/8$, and let $q_3$ be the raw constrained Schmidt-tangle profile. Then
--
--   $$
--   \tau(\rho_{3,F})=\begin{cases}0&F\le1/3,\\q_3(F)&1/3<F\le8/9,\\3(F-1)+4/3&8/9<F\le1,\end{cases}
--   \quad
--   C(\rho_{3,F})=\begin{cases}0&F\le1/3,\\\sqrt3(F-1/3)&1/3<F\le1.\end{cases}
--   $$
--
--   Moreover $q_3(8/9)=1$ and $q_3'(8/9)=3$. The equation $q_3'(x)=(4/3-q_3(x))/(1-x)$ has exactly the solution $x=8/9$ on $(1/3,1)$. An attaining tangle ensemble can have common pure tangle $\tau(\rho_{3,F})$ for $F\le8/9$, and pure tangles only in $\{1,4/3\}$ above $8/9$. An attaining concurrence ensemble can use only normalized product or maximally entangled states. These restrictions concern positive-weight members and do not require both types at an endpoint.
--
--   This explicit worked dimension illustrates the general tangent construction.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 11, §3.4.2, (3.38)–(3.39): two-qutrit formulas and tangent point

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.10--11, (3.38)--(3.39): explicit qutrit formulas, tangent data,
and attaining ensembles. Sqrt(3) multiplies the full displacement.
Zero-weight components are unrestricted; at F=1 no product component is required. -/
theorem two_qutrits (F : ℝ) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    tangle (isotropicDensityAtFidelity 3 F) =
      (if F ≤ 1/3 then 0 else if F ≤ 8/9 then explicitQ 3 F else 3*(F-1)+4/3) ∧
    concurrence (isotropicDensityAtFidelity 3 F) = (if F ≤ 1/3 then 0 else Real.sqrt 3 * (F-1/3)) ∧
    explicitQ 3 (8/9) = 1 ∧ deriv (explicitQ 3) (8/9) = 3 ∧
    (∀ x ∈ Set.Ioo (1/3 : ℝ) 1,
      (deriv (explicitQ 3) x = (4/3 - explicitQ 3 x) / (1-x) ↔ x = 8/9)) ∧
    (∃ e : PureEnsemble (Fin 3 × Fin 3), IsOptimalPureEnsemble pureTangle (isotropicDensityAtFidelity 3 F) e ∧
      ∀ k, 0 < e.weight k →
        if F ≤ 8/9 then pureTangle (e.vector k) = tangle (isotropicDensityAtFidelity 3 F)
        else pureTangle (e.vector k) = 1 ∨ pureTangle (e.vector k) = 4/3) ∧
    (∃ e : PureEnsemble (Fin 3 × Fin 3), IsOptimalPureEnsemble pureConcurrence (isotropicDensityAtFidelity 3 F) e ∧
      ∀ k, 0 < e.weight k → IsPureProductState (e.vector k) ∨ IsMaximallyEntangled (e.vector k)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
