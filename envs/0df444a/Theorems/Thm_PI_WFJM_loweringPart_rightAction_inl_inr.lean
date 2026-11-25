-- Prove2me | Theorems.Thm_PI_WFJM_loweringPart_rightAction_inl_inr
-- name    : PI.WFJM.loweringPart_rightAction_inl_inr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:14.611037+00:00
-- url     : https://prove2.me/theorems/dca67315-3117-4ebc-96a4-eb867793d14e
-- title:
--   WFJM: lowering Part right Action inl inr
-- statement:
--   The WFJM construction uses the lowering Part right Action inl inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L498-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L498-L509

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

theorem PI.WFJM.loweringPart_rightAction_inl_inr (k : Fin r) (l : Fin s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab (Sum.inl k) (Sum.inr l))) P = -(lapD (p := p) (q := q) k l P) := by sorry
