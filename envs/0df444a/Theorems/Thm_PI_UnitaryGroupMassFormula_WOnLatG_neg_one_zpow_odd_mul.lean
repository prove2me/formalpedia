-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_WOnLatG_neg_one_zpow_odd_mul
-- name    : PI.UnitaryGroupMassFormula.WOnLatG.neg_one_zpow_odd_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:52.955799+00:00
-- url     : https://prove2.me/theorems/c72f2f6a-2b66-56e8-a3e7-7616870b9a02
-- title:
--   WOn Lat G: neg one zpow odd mul
-- statement:
--   The WOn Lat G construction uses the neg one zpow odd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilLatticeAction/NegOneZpowOddMul.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilLatticeAction/NegOneZpowOddMul.lean#L12-L13

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

theorem PI.UnitaryGroupMassFormula.WOnLatG.neg_one_zpow_odd_mul {n : ℤ} (hn : Odd n) (m : ℤ) : (-1 : ℂ) ^ (n * m) = (-1 : ℂ) ^ m := by sorry
