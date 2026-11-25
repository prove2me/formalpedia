-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_differentiable_highest_weight_fn
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.differentiable_highest_weight_fn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:33:41.65171+00:00
-- url     : https://prove2.me/theorems/98437079-96c1-43f3-83d4-b2d003ed0af0
-- title:
--   HW: differentiable highest weight fn
-- statement:
--   The HW construction uses the differentiable highest weight fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L78-L81

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.differentiable_highest_weight_fn (ε : Fin n → Bool) (m : Fin n → ℤ) : Differentiable ℂ (f0 ε m) := by sorry
