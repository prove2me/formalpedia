-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_representativeNormBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.representativeNormBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:34:59.362966+00:00
-- url     : https://prove2.me/theorems/e946cb81-7040-4d9c-9af8-2d9bd81c270e
-- title:
--   IV.D, Eq.(4.44): trace-norm cb bound
-- statement:
--   Let $T$ be a complex-linear trace-class-preserving Bosonic transformation, with Weyl law $\chi_{T(X)}(z)=\chi_X(K^Tz)f(z)$ in regular irreducible finite-mode CCR representations. Suppose the defect form is nondegenerate and an invertible real coordinate change $A$ satisfies $\Delta''(z,w)=\Delta(A^{-1}z,A^{-1}w)$. Let $\rho$ be an actual Hermitian trace-class operator with $\operatorname{Tr}(\rho V(z))=f(Az)$. Then
--
--   $$\|T\|_\diamond\le\|\rho\|_1.$$
--
--   Neither $T$ nor $\rho$ is assumed positive or normalized. The norm is the full stabilized trace norm without a half factor. This provides the norm estimate from the representative's positive and negative parts.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 9, IV.D, Eq.(4.44): trace-norm cb bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- IV.D, (4.44), p.9: neither T nor its actual Hermitian representative
rho is assumed positive. A realizes the nondegenerate weylDefectPair. -/
theorem representativeNormBound {I J : Type} [Nonempty I] [Nonempty J]
    {s : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J s hbar)
    (T : Operation I J) (hT : TraceLinear T)
    (K : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ) (f : InterleavedPhase s → ℂ)
    (hlaw : LinearBosonic W Wout T K f) (A : InterleavedPhase s ≃ₗ[ℝ] InterleavedPhase s)
    (hA : ∀ z w, weylDefectPair hbar K z w =
      dotProduct (A.symm z) ((physicalCommutationMatrix s hbar).mulVec (A.symm w)))
    (rho : Matrix J J ℂ) (hrho : IsTraceClass rho)
    (hhermitian : ∀ i j, rho i j = star (rho j i))
    (hrepresentative : ∀ z, weylTraceCharacteristic Wout rho z = f (A z)) :
    stabilizedTraceClassNorm T ≤ traceSize rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
