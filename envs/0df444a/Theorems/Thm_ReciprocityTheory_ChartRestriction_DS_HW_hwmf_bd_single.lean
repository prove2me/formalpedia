-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_bd_single
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hwmf_bd_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:50:45.046388+00:00
-- url     : https://prove2.me/theorems/7d994283-6b96-4c49-86aa-20d5c6a16b95
-- title:
--   HW: hwmf bd single
-- statement:
--   The HW construction uses the hwmf bd single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L324-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L324-L331

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ReciprocityTheory.ChartRestriction.DS.HW.hwmf_bd_single (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) :
    bdPart ε (single a b (1 : ℂ)) = single a b 1 := by sorry
