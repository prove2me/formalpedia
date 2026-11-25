-- Prove2me | Theorems.Thm_PI_WFJM_minusPart2_expand
-- name    : PI.WFJM.minusPart2_expand
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:02.683694+00:00
-- url     : https://prove2.me/theorems/d075ce32-17c8-4664-8416-b23039a73eb6
-- title:
--   WFJM: minus Part2 expand
-- statement:
--   The WFJM construction uses the minus Part2 expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L541-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L541-L544

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
variable {p q r s : ℕ}

theorem PI.WFJM.minusPart2_expand (Y : Mat r s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Y) P = ∑ c, ∑ d, Y c d • minusPart (fockAct2 p q r s (Eab c d)) P := by sorry
