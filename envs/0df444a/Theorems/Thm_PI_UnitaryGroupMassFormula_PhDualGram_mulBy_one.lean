-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_mulBy_one
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.mulBy_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:31.397991+00:00
-- url     : https://prove2.me/theorems/2eb1f346-0b43-521b-8941-33f4a881fb0b
-- title:
--   Ph Dual Gram: mul By one
-- statement:
--   The Ph Dual Gram construction uses the mul By one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L31-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem PI.UnitaryGroupMassFormula.PhDualGram.mulBy_one (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} {x : MvPowerSeries σ ℂ_[p]}
    (hx : constantCoeff x = 0) : mulBy l ex 1 x = x := by sorry
