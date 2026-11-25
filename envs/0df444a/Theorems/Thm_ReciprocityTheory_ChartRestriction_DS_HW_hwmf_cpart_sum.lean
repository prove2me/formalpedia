-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_cpart_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hwmf_cpart_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:45.10594+00:00
-- url     : https://prove2.me/theorems/9cc68a9c-cb58-4c51-a119-fce1223e7b3d
-- title:
--   HW: hwmf cpart sum
-- statement:
--   The HW construction uses the hwmf cpart sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L136-L143

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.hwmf_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by sorry
