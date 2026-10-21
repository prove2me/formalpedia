-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_dilationCharacteristic
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.dilationCharacteristic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:34:30.933742+00:00
-- url     : https://prove2.me/theorems/13212374-95c3-4a9e-8449-0d9da4d41d73
-- title:
--   IV.B, Eqs.(4.39)–(4.40): dilation characteristic law
-- statement:
--   Fix a normalized environment density $\sigma_E$ and a unitary $U$ between completed system-environment tensor products. Suppose its bounded Weyl conjugation realizes the canonical system rows $R'=KR+K_E R_E$. Let $T(X)$ be the actual environment partial trace of $U(X\otimes\sigma_E)U^*$. Then $T$ is CPTP and, for every trace-class $X$,
--
--   $$\chi_{T(X)}(z)=\chi_X(K^Tz)\chi_{\sigma_E}(K_E^Tz),\qquad f(z)=\operatorname{Tr}(\sigma_E V_E(K_E^Tz)).$$
--
--   The representations are finite-mode regular irreducible CCR systems with positive $\hbar$. No input moments are needed. This identifies the multiplier of the fixed dilation.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 8, IV.B, Eqs.(4.39)–(4.40): dilation characteristic law

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

/-- IV.B, (4.39)--(4.40), pp.7--8: environment-weylTraceCharacteristic multiplier.
Witnesses precede all inputs. No input moment or positivity assumption is needed. -/
theorem dilationCharacteristic {I J E F : Type}
    [Nonempty I] [Nonempty J] [Nonempty E] [Nonempty F]
    {s t e : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J t hbar)
    (WE : ScaledWeylRepresentation E e hbar)
    (U : Hilbert (I × E) ≃ₗᵢ[ℂ] Hilbert (J × F)) (sigma : State E)
    (K : Matrix (Fin t × Fin 2) (Fin s × Fin 2) ℝ)
    (KE : Matrix (Fin t × Fin 2) (Fin e × Fin 2) ℝ)
    (hrows : CanonicalRows W Wout WE U K KE) :
    IsTraceClassChannel (unitaryTraceDilation U sigma.coefficients) ∧
    LinearBosonic W Wout (unitaryTraceDilation U sigma.coefficients) K
      (fun z => weylTraceCharacteristic WE sigma.coefficients (KE.transpose.mulVec z)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
