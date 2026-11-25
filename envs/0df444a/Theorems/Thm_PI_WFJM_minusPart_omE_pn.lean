-- Prove2me | Theorems.Thm_PI_WFJM_minusPart_omE_pn
-- name    : PI.WFJM.minusPart_omE_pn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:37.344186+00:00
-- url     : https://prove2.me/theorems/35a9d249-5813-46a1-bd36-1688576e95d2
-- title:
--   WFJM: minus Part om E pn
-- statement:
--   The WFJM construction uses the minus Part om E pn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L443-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L443-L449

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

theorem PI.WFJM.minusPart_omE_pn {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = true) (h' : linePos l' = false)
    (P : Pol p q r s) : minusPart (omE l l') P = 0 := by sorry
