-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_MV_inner_def
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.MV.inner_def
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:21.843363+00:00
-- url     : https://prove2.me/theorems/de2c6c13-53ad-4ff8-a91c-666f07a74d66
-- title:
--   MV: inner def
-- statement:
--   The MV construction uses the inner def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelInner.lean#L121-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelInner.lean#L121-L121

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.MV.inner_def {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : inner ℂ f g = mvInner f g := by sorry
