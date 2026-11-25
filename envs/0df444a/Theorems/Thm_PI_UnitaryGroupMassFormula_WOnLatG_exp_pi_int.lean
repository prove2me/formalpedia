-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_WOnLatG_exp_pi_int
-- name    : PI.UnitaryGroupMassFormula.WOnLatG.exp_pi_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:53.922421+00:00
-- url     : https://prove2.me/theorems/d058853b-529f-45a5-8db5-988bf2f2c507
-- title:
--   WOn Lat G: exp pi int
-- statement:
--   The WOn Lat G construction uses the exp pi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilLatticeAction/NegOneZpowOddMul.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilLatticeAction/NegOneZpowOddMul.lean#L7-L10

import Definitions.Def_Formalism_PeriodIntegrals_WOnLatG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilLatticeAction_NegOneZpowOddMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.WOnLatG
open PI.WPhDefs

theorem PI.UnitaryGroupMassFormula.WOnLatG.exp_pi_int (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by sorry
