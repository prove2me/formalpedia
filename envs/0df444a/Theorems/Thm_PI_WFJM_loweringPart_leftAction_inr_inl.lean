-- Prove2me | Theorems.Thm_PI_WFJM_loweringPart_leftAction_inr_inl
-- name    : PI.WFJM.loweringPart_leftAction_inr_inl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:15.775539+00:00
-- url     : https://prove2.me/theorems/27a4cee3-d39b-5068-8d29-d1ac6aff6e7a
-- title:
--   WFJM: lowering Part left Action inr inl
-- statement:
--   The WFJM construction uses the lowering Part left Action inr inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L485-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L485-L496

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

theorem PI.WFJM.loweringPart_leftAction_inr_inl (i : Fin p) (j : Fin q) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s (Eab (Sum.inr j) (Sum.inl i))) P = -(lapB (r := r) (s := s) i j P) := by sorry
