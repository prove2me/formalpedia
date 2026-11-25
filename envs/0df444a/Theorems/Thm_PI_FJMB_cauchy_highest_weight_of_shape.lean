-- Prove2me | Theorems.Thm_PI_FJMB_cauchy_highest_weight_of_shape
-- name    : PI.FJMB.cauchy_highest_weight_of_shape
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:08.023829+00:00
-- url     : https://prove2.me/theorems/e1ea6b96-ca11-4a1b-ada9-6949b5844fea
-- title:
--   FJMB: cauchy highest weight of shape
-- statement:
--   The FJMB construction uses the cauchy highest weight of shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauchyHighestWeightOfShape.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauchyHighestWeightOfShape.lean#L6-L9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHighestWeightOfShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJMB

theorem PI.FJMB.cauchy_highest_weight_of_shape (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by sorry
