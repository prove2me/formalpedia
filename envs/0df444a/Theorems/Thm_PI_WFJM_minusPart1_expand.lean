-- Prove2me | Theorems.Thm_PI_WFJM_minusPart1_expand
-- name    : PI.WFJM.minusPart1_expand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:22.247646+00:00
-- url     : https://prove2.me/theorems/4d7f4b25-5638-42f8-9619-fe16b9467067
-- title:
--   WFJM: minus Part1 expand
-- statement:
--   The WFJM construction uses the minus Part1 expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L536-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L536-L539

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

theorem PI.WFJM.minusPart1_expand (X : Mat p q) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s X) P = ∑ a, ∑ b, X a b • minusPart (fockAct1 p q r s (Eab a b)) P := by sorry
