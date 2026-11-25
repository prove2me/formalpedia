-- Prove2me | Theorems.Thm_PI_FJMX_negPart_getD
-- name    : PI.FJMX.negPart_getD
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:01.578131+00:00
-- url     : https://prove2.me/theorems/7413b56b-f651-49da-bbb6-68ffc8ee7864
-- title:
--   FJMX: neg Part get D
-- statement:
--   The FJMX construction uses the neg Part get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistPad.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistPad.lean#L28-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX

theorem PI.FJMX.negPart_getD (b : List ℤ) (hb : ∀ v ∈ b, v < 0) (j : ℕ) :
    ((PI.FJM.negPart b).getD j 0 : ℚ) =
      if h : j < b.length then -((b[b.length - 1 - j]'(by omega) : ℤ) : ℚ) else 0 := by sorry
