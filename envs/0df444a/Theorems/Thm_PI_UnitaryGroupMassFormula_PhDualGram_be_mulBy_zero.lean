-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_be_mulBy_zero
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.be_mulBy_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:36.642035+00:00
-- url     : https://prove2.me/theorems/9c23f91a-4092-546d-93d0-acd1b653565f
-- title:
--   Ph Dual Gram: be mul By zero
-- statement:
--   The Ph Dual Gram construction uses the be mul By zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L38-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_FglPhSplit_Wk_be_mulBy_zero

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.be_mulBy_zero (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} (x : MvPowerSeries σ ℂ_[p])
    {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    be l ex ph (mulBy l ex 0 x) y = 0 := by sorry
