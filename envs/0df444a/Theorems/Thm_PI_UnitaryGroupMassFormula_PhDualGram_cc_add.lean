-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_add
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.cc_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:12.951594+00:00
-- url     : https://prove2.me/theorems/9ac7a823-2b51-4328-9808-52f229ea1f57
-- title:
--   Ph Dual Gram: cc add
-- statement:
--   The Ph Dual Gram construction uses the cc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L13-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_FglPhSplit_Wk_cc_add

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.cc_add (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ : Type} {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (add l ex x y) = 0 := by sorry
