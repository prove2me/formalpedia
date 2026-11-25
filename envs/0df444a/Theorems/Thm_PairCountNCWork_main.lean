-- Prove2me | Theorems.Thm_PairCountNCWork_main
-- name    : PairCountNCWork.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:45.871787+00:00
-- url     : https://prove2.me/theorems/1dc78f19-083e-437f-bb7d-d1a2a2850cf1
-- title:
--   Pair Count NCWork: main
-- statement:
--   The Pair Count NCWork construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PairCountNoncommuting/OtherFalse.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PairCountNoncommuting/OtherFalse.lean#L49-L53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PairCountNoncommuting_OtherFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PairCountNCWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool)

theorem PairCountNCWork.main : cBCardNC := by sorry
