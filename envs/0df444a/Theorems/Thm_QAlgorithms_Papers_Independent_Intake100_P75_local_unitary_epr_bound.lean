-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_local_unitary_epr_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.local_unitary_epr_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:03:15.757083+00:00
-- url     : https://prove2.me/theorems/b3b241d3-dfcf-4bf5-ab79-5aa3510c5e8d
-- title:
--   Local-unitary separability invariance and variance witness
-- statement:
--   Let $\rho$ be any normalized two-mode density and let $U=U_1\otimes U_2$ for arbitrary local unitaries on the completed oscillator spaces. Then
--
--   $$
--   U\rho U^\dagger\text{ is separable}\quad\Longleftrightarrow\quad\rho\text{ is separable}.
--   $$
--
--   Separability uses the trace-norm closed convex hull of normalized product densities. For every nonzero real $a$, define $u=|a|x_1+x_2/a$ and $v=|a|p_1-p_2/a$ using $[x_j,p_k]=i\delta_{jk}$. If $\rho$ is separable, then
--
--   $$
--   \operatorname{Var}_{\rho}(UuU^\dagger)+\operatorname{Var}_{\rho}(UvU^\dagger)\ge a^2+a^{-2}.
--   $$
--
--   The extended variances transport the full unbounded-operator domains. The local operations may be non-Gaussian. The statement also asserts square-summable realization of both forward and inverse tensor-unitary actions.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 2, Paragraph after Theorem 1, p.2; LLUBO-invariance remark, p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P75

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P75

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable IsBarycenter rankOne productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl CharacteristicSummable multimodeWeylTrace
   covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Next46.P45
  (TwoMode PureVector Decomposes ladderCoefficients squeezedVector
   squeezedCoefficients GaussianShiftLaw shiftArgument)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel partialRight)

open QAlgorithms.Papers.Independent.Frontier18.P14 (occupationOutput)

open QAlgorithms.Papers.Independent.Gap48.P26 (thermalKernel)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.2, paragraph after Theorem 1, and p.4, LLUBO-invariance remark:
actual local-unitary density conjugation preserves separability in both directions.
For every separable input the variance-witness bound holds on the conjugated
observables in the fixed state. Domains are transported by inverse tensor
unitaries; realization excludes all fallbacks. -/
theorem local_unitary_epr_bound
    (rho : State (FockIndex 2)) (a : ℝ) (ha : a ≠ 0)
    (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1)) :
    (∀ psi : TwoMode, Memℓp (tensorImageCoefficients U V psi) 2 ∧
      Memℓp (tensorImageCoefficients U.symm V.symm psi) 2) ∧
    (IsSeparable (pairedKernel
        (conjugateKernel (tensorUnitaryKernel U V) rho.coefficients)) ↔
      IsSeparable (pairedKernel rho.coefficients)) ∧
    (IsSeparable (pairedKernel rho.coefficients) →
      ENNReal.ofReal (a ^ 2 + 1 / a ^ 2) ≤
        varianceOfForm (transportedEprForm U V false a) rho.coefficients +
          varianceOfForm (transportedEprForm U V true a) rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
