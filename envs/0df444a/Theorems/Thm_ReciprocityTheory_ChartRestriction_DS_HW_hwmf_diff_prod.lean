-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_diff_prod
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hwmf_diff_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:49.78604+00:00
-- url     : https://prove2.me/theorems/1b602687-a9b7-45d9-86f7-058fe5a59ad4
-- title:
--   HW: hwmf diff prod
-- statement:
--   The HW construction uses the hwmf diff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L56-L64

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.hwmf_diff_prod {ι : Type} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i, Differentiable ℂ (g i)) : Differentiable ℂ (fun x => ∏ i ∈ s, g i x) := by sorry
