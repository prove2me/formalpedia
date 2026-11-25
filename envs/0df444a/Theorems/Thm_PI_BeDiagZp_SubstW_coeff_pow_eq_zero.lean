-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_coeff_pow_eq_zero
-- name    : PI.BeDiagZp.SubstW.coeff_pow_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:49.333108+00:00
-- url     : https://prove2.me/theorems/1798ecc2-3196-40e0-8874-6c3ec0458fd9
-- title:
--   Subst W: coeff pow eq zero
-- statement:
--   The Subst W construction uses the coeff pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L98-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.SubstW.coeff_pow_eq_zero {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) {n : ℕ} {d : σ →₀ ℕ} (h : d.degree < n) :
    MvPowerSeries.coeff d (F ^ n) = 0 := by sorry
