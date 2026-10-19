-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_halfTransmissivityOverlap
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.halfTransmissivityOverlap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:22:32.917262+00:00
-- url     : https://prove2.me/theorems/59a15035-24ea-4f11-84f0-fbf55e9d7a52
-- title:
--   The 50/50 beam splitter has both properties
-- statement:
--   Fix a centered Gaussian environmental density $\sigma$ and a bounded joint unitary $U$ implementing the source’s standard matrix at intensity parameter $k$. Write $E_{U,\sigma}$ and $F_{U,\sigma}$ for its receiver and weak complement. At $k=1/2$, the receiver satisfies
--
--   $$\mathrm{WD}(E_{U,\sigma},F_{U,\sigma})\ \land\ \mathrm{AD}(E_{U,\sigma},F_{U,\sigma}).$$
--
--   Both recoveries are full trace-class CPTP maps working for every input density. This records the overlap of the two threshold branches. It does not assert equality of the receiver and environmental channels: their input characteristic-function arguments have opposite signs.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 3, Table I, also §II and §IV

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section II/Table I/Section IV, PDF pp.2-4: the 50/50 beam splitter has both
properties, without equality of its two output maps on arbitrary inputs. -/
theorem halfTransmissivityOverlap (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)))
    (hcanonical : Canonical U (standardMatrix (1 / 2)))
    (sigma : State ℕ) (hcentered : CenteredGaussian sigma.coefficients) :
    WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ∧
    AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
