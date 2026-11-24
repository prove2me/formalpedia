-- Prove2me | Theorems.Thm_PI_WFJM_minusPart_smul
-- name    : PI.WFJM.minusPart_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:32.581675+00:00
-- url     : https://prove2.me/theorems/93a9a56e-913b-43a3-8c27-e102ee555268
-- title:
--   WFJM: minus Part smul
-- statement:
--   The WFJM construction uses the minus Part smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L376-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L376-L378

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
open MvPolynomial
variable {σ : Type*}

theorem PI.WFJM.minusPart_smul (c : ℂ) (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart (c • A) P = c • minusPart A P := by sorry
