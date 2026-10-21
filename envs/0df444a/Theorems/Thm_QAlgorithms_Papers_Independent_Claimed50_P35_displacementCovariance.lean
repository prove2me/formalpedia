-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_displacementCovariance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.displacementCovariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:33:59.350686+00:00
-- url     : https://prove2.me/theorems/efbaf5b5-89cd-4449-b0aa-98a1286aebdd
-- title:
--   IV.A, property (C): displacement covariance
-- statement:
--   Let $T$ be a fixed linear Bosonic CPTP channel between finite-mode regular irreducible CCR systems, with $T^*(V'(w))=V(K^Tw)f(w)$ and $\hbar>0$. For any normalized input density $\rho$ and displacement $z$, define $\rho_z=V(-\Delta^{-1}z)\rho V(-\Delta^{-1}z)^*$. Then
--
--   $$T(\rho_z)=V'(-\Delta'^{-1}Kz)T(\rho)V'(-\Delta'^{-1}Kz)^*.$$
--
--   No Gaussian or moment hypothesis is imposed on $\rho$. This expresses covariance under the source's phase-space translation convention.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 7, IV.A, property (C): displacement covariance

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

/-- IV.A(C), p.7: covariance for all densities, without Gaussian/moment assumptions. -/
theorem displacementCovariance {I J : Type} [Nonempty I] [Nonempty J]
    {s t : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J t hbar)
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (K : Matrix (Fin t × Fin 2) (Fin s × Fin 2) ℝ) (f : InterleavedPhase t → ℂ)
    (hlaw : LinearBosonic W Wout T K f) (rho : State I) (z : InterleavedPhase s) :
    T (phaseSpaceShift W z rho.coefficients) = phaseSpaceShift Wout (K.mulVec z) (T rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
