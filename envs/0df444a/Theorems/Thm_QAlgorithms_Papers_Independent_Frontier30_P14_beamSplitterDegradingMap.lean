-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_beamSplitterDegradingMap
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.beamSplitterDegradingMap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:21:32.19699+00:00
-- url     : https://prove2.me/theorems/9f913f7d-9f40-4c83-98fd-e80bc4478110
-- title:
--   Explicit degrading beam-splitter complement
-- statement:
--   Fix a centered Gaussian environmental density $\sigma$ and a bounded joint unitary $U$ implementing the source’s standard matrix at intensity parameter $k$. Write $E_{U,\sigma}$ and $F_{U,\sigma}$ for its receiver and weak complement. If $1/2\le k\le1$, there exists a bounded beam-splitter coupling $V$ of transmissivity $k'=(2k-1)/k\in[0,1]$. Its weak complement is CPTP and, for every input density,
--
--   $$F_{U,\sigma}(\rho)=F_{V,\sigma}(E_{U,\sigma}(\rho)).$$
--
--   Consequently the receiver is weakly degradable, including both endpoints. The auxiliary environment is an independent copy of $\sigma$. At $k=1/2$ the auxiliary weak complement includes parity; the theorem does not identify the two original output maps.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 4, §IV, (19)-(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section IV, (19)-(20), PDF p.4: both beam-splitter endpoints are included.
The auxiliary transmissivity is (2k-1)/k; at k=1/2 its weak complement is parity,
so equality of the dilationReceiver and environmental maps is not asserted. -/
theorem beamSplitterDegradingMap (k : ℝ) (hlo : (1 / 2 : ℝ) ≤ k) (hhi : k ≤ 1)
    (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (hcanonical : Canonical U (standardMatrix k))
    (sigma : State ℕ) (hcentered : CenteredGaussian sigma.coefficients) :
    WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ∧
    ∃ V : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)), Canonical V (standardMatrix ((2 * k - 1) / k)) ∧
      IsTraceClassChannel (weakComplement V sigma.coefficients) ∧
      ∀ rho : State ℕ, weakComplement U sigma.coefficients rho.coefficients =
        weakComplement V sigma.coefficients (dilationReceiver U sigma.coefficients rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
