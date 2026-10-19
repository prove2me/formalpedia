-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_antidegradableZeroCapacity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.antidegradableZeroCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:19:59.409231+00:00
-- url     : https://prove2.me/theorems/417783c4-b2f9-46f7-b5d8-83cd308cc1f4
-- title:
--   Anti-degradability forces zero operational quantum capacity
-- statement:
--   Let $U$ be a bounded joint unitary on the completed carrier/environment spaces, let $\sigma$ be an environmental density, and let $E,F$ be the resulting receiver and environmental channels. If some full trace-class CPTP map $T$ satisfies $T(F(\rho))=E(\rho)$ for every input density $\rho$, then the unassisted operational quantum capacity satisfies
--
--   $$Q(E)=0.$$
--
--   Capacity is the extended nonnegative supremum of achievable qubit rates using arbitrary CPTP encoders and decoders over arbitrarily many independent uses, with entanglement-transmission fidelity tending to one. No energy constraint is imposed. This is the paper’s stated no-cloning consequence.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 2, §II, no-cloning paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section II, PDF p.2, no-cloning consequence: operational, unconstrained
quantum capacity vanishes for anti-degradable channels. -/
theorem antidegradableZeroCapacity {I J : Type} [Nonempty I]
    (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : State J)
    (hanti : AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) :
    operationalTraceClassCapacity (dilationReceiver U sigma.coefficients) = 0 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
