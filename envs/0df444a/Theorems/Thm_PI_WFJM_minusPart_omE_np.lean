-- Prove2me | Theorems.Thm_PI_WFJM_minusPart_omE_np
-- name    : PI.WFJM.minusPart_omE_np
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:50.852042+00:00
-- url     : https://prove2.me/theorems/27cc1f49-93ff-4dc2-a5ac-a1b1463b02d9
-- title:
--   WFJM: minus Part om E np
-- statement:
--   The WFJM construction uses the minus Part om E np property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L451-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L451-L462

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

theorem PI.WFJM.minusPart_omE_np {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = false) (h' : linePos l' = true)
    (P : Pol p q r s) : minusPart (omE l l') P = -(dd l l' P) := by sorry
