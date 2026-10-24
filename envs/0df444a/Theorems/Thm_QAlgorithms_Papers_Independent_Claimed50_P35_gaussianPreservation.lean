-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_gaussianPreservation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.gaussianPreservation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:33:06.781725+00:00
-- url     : https://prove2.me/theorems/d53dee3a-a95f-4181-8706-8f438076092a
-- title:
--   IV.A, property (B): Gaussian preservation
-- statement:
--   Let $T$ be a fixed finite-mode CPTP channel whose normal Weyl action is $T^*(V'(z))=V(K^Tz)\exp(i d^Tz-z^TBz/2)$, with real $K,d$ and symmetric real $B$. Use regular irreducible CCR representations with $\hbar>0$. If a normalized input density $\rho$ has Gaussian characteristic function $\exp(i m^Tz-z^T\alpha z/2)$, with real symmetric $\alpha$, then $T(\rho)$ is a normalized Gaussian density and
--
--   $$\chi_{T(\rho)}(z)=\exp\!\left(i(Km+d)^Tz-\tfrac12 z^T(K\alpha K^T+B)z\right).$$
--
--   The channel and its multiplier precede every input. This is Gaussian preservation with the resulting parameters explicitly computed.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 7, IV.A, property (B): Gaussian preservation

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

/-- IV.A(B), p.7: Gaussian preservation, with computed mean and covariance. -/
theorem gaussianPreservation {I J : Type} [Nonempty I] [Nonempty J]
    {s t : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J t hbar)
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (K : Matrix (Fin t × Fin 2) (Fin s × Fin 2) ℝ)
    (d : InterleavedPhase t) (B : Matrix (Fin t × Fin 2) (Fin t × Fin 2) ℝ)
    (hB : B.transpose = B) (hlaw : LinearBosonic W Wout T K (gaussianFunction d B))
    (rho : State I) (m : InterleavedPhase s)
    (alpha : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ)
    (halpha : alpha.transpose = alpha)
    (hrho : ∀ z, weylTraceCharacteristic W rho.coefficients z = gaussianFunction m alpha z) :
    MultimodeGaussianDensity Wout (T rho.coefficients) ∧
    ∀ z, weylTraceCharacteristic Wout (T rho.coefficients) z =
      gaussianFunction (K.mulVec m + d) (K * alpha * K.transpose + B) z := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
