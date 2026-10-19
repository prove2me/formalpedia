-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_amplifierDegradingMap
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.amplifierDegradingMap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:21:09.40398+00:00
-- url     : https://prove2.me/theorems/0694a8ed-6e3d-4334-868d-feb9be1676df
-- title:
--   Explicit degrading amplifier complement
-- statement:
--   Fix a centered Gaussian environmental density $\sigma$ and a bounded joint unitary $U$ implementing the source’s standard matrix at intensity parameter $k$. Write $E_{U,\sigma}$ and $F_{U,\sigma}$ for its receiver and weak complement. If $k\ge1$, there exists a bounded amplifier coupling $V$ of gain $k'=(2k-1)/k\ge1$. Its weak complement is CPTP and, for every input density,
--
--   $$F_{U,\sigma}(\rho)=F_{V,\sigma}(E_{U,\sigma}(\rho)).$$
--
--   Thus $E_{U,\sigma}$ is weakly degradable. Each stage uses an independent environment with the same density $\sigma$; neither the coupling nor the recovery depends on $\rho$. This specifies the recovery map rather than merely asserting recoverability.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 4, §IV, (18)-(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section IV, (18)-(19), PDF p.4: the recovery is the weak complement of an
amplifier of gain (2k-1)/k. The auxiliary coupling is constructed existentially;
its CPTP property and the cascade identity are conclusions, not hypotheses. -/
theorem amplifierDegradingMap (k : ℝ) (hk : 1 ≤ k)
    (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (hcanonical : Canonical U (standardMatrix k))
    (sigma : State ℕ) (hcentered : CenteredGaussian sigma.coefficients) :
    WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ∧
    ∃ V : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)), Canonical V (standardMatrix ((2 * k - 1) / k)) ∧
      IsTraceClassChannel (weakComplement V sigma.coefficients) ∧
      ∀ rho : State ℕ, weakComplement U sigma.coefficients rho.coefficients =
        weakComplement V sigma.coefficients (dilationReceiver U sigma.coefficients rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
