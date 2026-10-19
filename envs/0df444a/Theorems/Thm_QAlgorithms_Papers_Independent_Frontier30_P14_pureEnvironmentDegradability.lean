-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_pureEnvironmentDegradability
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.pureEnvironmentDegradability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:19:18.822773+00:00
-- url     : https://prove2.me/theorems/a1f62317-b01c-4f58-afe3-12c2d776412d
-- title:
--   Pure environment: equivalence with ordinary degradability
-- statement:
--   Fix a bounded joint unitary $U$ and an environmental density $\sigma$, and let $E,F$ be its receiver and weak complement. Ordinary degradability means CPTP recoverability of a true complement of a pure Stinespring isometry. Then
--
--   $$
--   \sigma\text{ pure}\ \Longrightarrow\
--   \bigl(\mathrm{WD}(E,F)\iff E\text{ ordinarily degradable}\bigr),
--   $$
--   $$
--   E\text{ ordinarily degradable}\ \Longrightarrow\ \mathrm{WD}(E,F)
--   \quad\text{for arbitrary }\sigma.
--   $$
--
--   Purity means a normalized rank-one density. Every recovery acts on all densities of the complete spaces. This identifies the two notions in the pure case and retains only the necessary direction for a mixed representation; it makes no coherent-information claim.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 2, §II, paragraph following (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section II, PDF p.2: equivalence for a pure environment, and only necessity
for an arbitrary mixed representation. Ordinary degradability uses a true pure
Stinespring isometry; it is not defined using the mixed weak complement. -/
theorem pureEnvironmentDegradability {I J : Type} [Nonempty I]
    (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : State J) :
    (PureDensity sigma.coefficients →
      (WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ↔
        OrdinarilyDegradable (dilationReceiver U sigma.coefficients))) ∧
    (OrdinarilyDegradable (dilationReceiver U sigma.coefficients) →
      WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
