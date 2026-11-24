-- Prove2me | Theorems.Thm_PI_QnZeroLevelWork_skip_two_succAbove_comp_alt
-- name    : PI.QnZeroLevelWork.skip_two_succAbove_comp_alt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:23.886396+00:00
-- url     : https://prove2.me/theorems/41531401-ce31-4409-bfdd-fcd7a95c82a6
-- title:
--   Qn Zero Level Work: skip two succ Above comp alt
-- statement:
--   The Qn Zero Level Work construction uses the skip two succ Above comp alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L26-L33

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem PI.QnZeroLevelWork.skip_two_succAbove_comp_alt {t : ℕ} (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t) (hii : i.val ≤ i'.val) :
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j) := by sorry
