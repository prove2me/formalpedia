-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_det_star_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.twist_det_star_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:11.921604+00:00
-- url     : https://prove2.me/theorems/224cb9f1-e047-4f6e-ae3f-e2492d9a11c3
-- title:
--   HW: twist det star mul
-- statement:
--   The HW construction uses the twist det star mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelTwist.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelTwist.lean#L14-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.twist_det_star_mul {ε : Fin n → Bool} (k : KG ε) : star (toMK k).det * (toMK k).det = 1 := by sorry
