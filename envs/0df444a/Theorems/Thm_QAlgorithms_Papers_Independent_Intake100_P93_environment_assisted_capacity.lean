-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_environment_assisted_capacity
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.environment_assisted_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:40:34.119241+00:00
-- url     : https://prove2.me/theorems/52c2ce27-a58b-4594-aac1-af18792761ef
-- title:
--   Theorem 8: environment-assisted quantum capacity
-- statement:
--   Let $U:A\to B\otimes C$ be an isometry between nonzero finite-dimensional spaces and $T(\rho)=\operatorname{Tr}_C(U\rho U^\dagger)$ the transmitted channel. The environment helper may collectively measure $C^n$ and forward its outcome to the receiver. Alice encodes unknown quantum information into $n$ uses, and Bob decodes according to the helper's classical message. No honest-party shared entanglement or additional quantum communication is available. Then
--
--   $$C_A(T)=\max_{\rho\text{ a density state on }A}\min\{S(\rho),S(T(\rho))\}.$$
--
--   The maximum is attained. The same threshold describes the capacity when the three honest parties may use unrestricted LOCC. Transmission is tested jointly with an untouched external purifying reference, at all sufficiently large positive blocklengths with vanishing error. This is a quantum communication capacity, with environment messages as assistance.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 5, Theorem 8: environment-assisted quantum capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF pp.4--5, Theorem 8: environment-assisted capacity, including equality
when unlimited LOCC is allowed. The maximum is attained by a genuine input
state. The dilation is the channel's environment access, not extra entanglement. -/
theorem environment_assisted_capacity {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (U : Matrix (Fin b × Fin c) (Fin a) ℂ) (hU : Uᴴ * U = 1) :
    (∃ rho : Op (Fin a), IsDensityMatrix rho ∧
      assistedCapacityObjective (receiverChannel U) =
        min (vnEntropy rho) (vnEntropy (receiverChannel U rho))) ∧
    ∀ r : ℝ,
      (TransmissionRate U false r ↔ 0 ≤ r ∧ r ≤ assistedCapacityObjective (receiverChannel U)) ∧
      (TransmissionRate U true r ↔ 0 ≤ r ∧ r ≤ assistedCapacityObjective (receiverChannel U)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
