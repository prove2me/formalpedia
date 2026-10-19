-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_beamSplitterAntidegradingMap
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.beamSplitterAntidegradingMap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:21:58.024649+00:00
-- url     : https://prove2.me/theorems/2b171d45-22f0-4a4c-bc51-058d96f12051
-- title:
--   Explicit anti-degrading beam-splitter complement
-- statement:
--   Fix a centered Gaussian environmental density $\sigma$ and a bounded joint unitary $U$ implementing the source’s standard matrix at intensity parameter $k$. Write $E_{U,\sigma}$ and $F_{U,\sigma}$ for its receiver and weak complement. If $0\le k\le1/2$, there exists a bounded beam-splitter coupling $V$ of transmissivity $k''=(1-2k)/(1-k)\in[0,1]$. Its weak complement is CPTP and, for every input density,
--
--   $$E_{U,\sigma}(\rho)=F_{V,\sigma}(F_{U,\sigma}(\rho)).$$
--
--   Consequently the receiver is anti-degradable, including $k=0$ and $k=1/2$. The denominator is positive throughout this interval. Each use has an independent environment of density $\sigma$; the recovery works uniformly for all inputs.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 4, §IV, (21)-(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section IV, (21)-(22), PDF p.4: both k=0 and k=1/2 are included.
Independent auxiliary environments have exactly the original density sigma. -/
theorem beamSplitterAntidegradingMap (k : ℝ) (hlo : 0 ≤ k) (hhi : k ≤ (1 / 2 : ℝ))
    (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (hcanonical : Canonical U (standardMatrix k))
    (sigma : State ℕ) (hcentered : CenteredGaussian sigma.coefficients) :
    AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ∧
    ∃ V : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)), Canonical V (standardMatrix ((1 - 2 * k) / (1 - k))) ∧
      IsTraceClassChannel (weakComplement V sigma.coefficients) ∧
      ∀ rho : State ℕ, dilationReceiver U sigma.coefficients rho.coefficients =
        weakComplement V sigma.coefficients (weakComplement U sigma.coefficients rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
