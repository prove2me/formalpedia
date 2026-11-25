-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GramUnit_be_mulBy_zero
-- name    : PI.UnitaryGroupMassFormula.GramUnit.be_mulBy_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:50.55914+00:00
-- url     : https://prove2.me/theorems/3ba7a084-8e9a-415a-a6db-1f707f5ef98c
-- title:
--   Gram Unit: be mul By zero
-- statement:
--   The Gram Unit construction uses the be mul By zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramUnitMultiplication/BeMulByZero.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramUnitMultiplication/BeMulByZero.lean#L43-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramUnit
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]

theorem PI.UnitaryGroupMassFormula.GramUnit.be_mulBy_zero (l ex ph : PowerSeries ℂ_[p]) (hD : Data l ex ph) {σ : Type*}
    (a b : MvPowerSeries σ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    be l ex ph (mulBy l ex 0 a) b = 0 := by sorry
