-- Prove2me | Theorems.Thm_PI_QnCovHat2W_skip_two_of_lt
-- name    : PI.QnCovHat2W.skip_two_of_lt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:31.417645+00:00
-- url     : https://prove2.me/theorems/206cc818-81b6-49e7-b89b-dfc01017dbe6
-- title:
--   Qn Cov Hat2 W: skip two of lt
-- statement:
--   The Qn Cov Hat2 W construction uses the skip two of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L102-L107

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovHat2W.skip_two_of_lt {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : Fin.castSucc j' < j) :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 (Fin.castSucc j') j := by sorry
