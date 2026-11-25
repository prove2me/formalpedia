-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_WOnLatG_main
-- name    : PI.UnitaryGroupMassFormula.WOnLatG.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:15.22961+00:00
-- url     : https://prove2.me/theorems/edd62a49-7b68-53af-b476-abfc7bdfc46a
-- title:
--   WOn Lat G: main
-- statement:
--   The WOn Lat G construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilLatticeAction/NegOneZpowOddMul.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilLatticeAction/NegOneZpowOddMul.lean#L15-L36

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

theorem PI.UnitaryGroupMassFormula.WOnLatG.main : PI.WOnLatG := by sorry
