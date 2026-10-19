-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_weakComplementDuality
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.weakComplementDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:18:18.306319+00:00
-- url     : https://prove2.me/theorems/9fc1b1d6-4f76-40b2-bea0-980933ffc2e6
-- title:
--   Duality for the same two output legs
-- statement:
--   Fix a bounded joint unitary $U$ on the completed carrier/environment product and an environmental density $\sigma$. Let $E(\rho)=\operatorname{Tr}_b U(\rho\otimes\sigma)U^\dagger$ and $\widetilde E(\rho)=\operatorname{Tr}_a U(\rho\otimes\sigma)U^\dagger$. Then
--
--   $$E\text{ is weakly degradable relative to }\widetilde E
--   \quad\Longleftrightarrow\quad
--   \widetilde E\text{ is anti-degradable relative to }E.$$
--
--   Both predicates require a single CPTP recovery working for every density on the complete input space. This duality concerns the same represented pair, even when $\sigma$ is mixed.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 2, §II, following (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section II, PDF p.2: duality refers to the same two output legs of the same
representation; mixed weak complements are not Stinespring complements. -/
theorem weakComplementDuality {I J : Type} [Nonempty I]
    (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : State J) :
    WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ↔
      AntiDegradable (weakComplement U sigma.coefficients) (dilationReceiver U sigma.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
