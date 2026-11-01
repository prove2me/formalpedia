-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_zeroEntanglementHeterodyne
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.zeroEntanglementHeterodyne
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:22:13.164301+00:00
-- url     : https://prove2.me/theorems/1f3a0b05-a325-4c46-88ba-95ffae9ebf43
-- title:
--   Zero-entanglement optimum and heterodyne preparation
-- statement:
--   For every finite $\lambda>0$, zero shared entanglement gives the Gaussian optimum
--
--   $$g=\frac1{1+\lambda},\qquad \tau_{\rm opt}=g^2=\frac1{(1+\lambda)^2},\qquad y_{\rm opt}=1+\tau_{\rm opt},\qquad \overline F_{\rm opt}=\frac{1+\lambda}{2+\lambda}.$$
--
--   The minimum-energy resource family (9) has $a=b=1$, $c=0$: it is the actual two-mode vacuum with zero photon energy and partial-transpose trace norm one. The BK map is heterodyne detection on the input followed by preparation of $|g\beta\rangle$ for outcome $\beta$. Explicitly, the channel is the coefficientwise integral of $|g\beta\rangle\langle g\beta|$ against $\langle\beta|\rho|\beta\rangle d^2\beta/\pi$; all such coefficient integrands are integrable. It is the phase-insensitive channel with the displayed parameters and actual average fidelity.
--
--   The transmissivity corrects the printed (14), which conflicts with $\tau=g^2$ in (7) and the gain in its own paragraph. The recovered Gaussian specialization is stated, while the older unrestricted classical benchmark [25] and implementation [7] retain their provenance.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 4, Zero-entanglement specialization and optimal heterodyne gain, Eq. (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)

open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)

open QAlgorithms.Entanglement (partialTransposeFirst)

/-- PDF p.4, (14), CORRECTED: printed tau=(1+lambda)^(-1) is replaced
by tau=(1+lambda)^(-2), because (7) and the same paragraph give g=(1+lambda)^(-1).
This is the Gaussian specialization and its heterodyne implementation, not a
new claim about the independently cited unrestricted classical benchmark. -/
theorem zeroEntanglementHeterodyne (lambda : ℝ) (hlambda : 0 < lambda) :
    let g := (1 + lambda)⁻¹
    let tau := ((1 + lambda)⁻¹) ^ 2
    optimalTau lambda 0 = tau ∧ optimalNoise lambda 0 = 1 + tau ∧
    scalarOptimum lambda 0 = (1 + lambda) / (2 + lambda) ∧
    familyMinA 0 tau = 1 ∧ familyMinB 0 tau = 1 ∧ familyMinC 0 tau = 0 ∧
    (∃ rho : State (ℕ × ℕ),
      rho.coefficients = tmssKernel 0 ∧
      CenteredResource rho (standardFormCovariance 1 1 0 0) ∧ twoModeMeanPhotonEnergy rho = 0 ∧
      traceSize (partialTransposeFirst rho.coefficients) = 1 ∧
      IsBK rho g (heterodynePrepare g)) ∧
    PhaseInsensitive (heterodynePrepare g) tau (1 + tau) ∧
    gaussianPriorFidelity lambda (heterodynePrepare g) = (1 + lambda) / (2 + lambda) ∧
    (∀ (rho : State ℕ) (m n : ℕ), Integrable (fun beta : ℂ =>
      (inner (𝕜 := ℂ) (coherentKet beta) ((operatorOfMatrix rho.coefficients) (coherentKet beta)) /
        (Real.pi : ℂ)) * coherentKernel ((g : ℂ) * beta) m n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
