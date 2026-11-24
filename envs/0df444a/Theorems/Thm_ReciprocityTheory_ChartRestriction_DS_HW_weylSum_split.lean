-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_split
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylSum_split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:25.47545+00:00
-- url     : https://prove2.me/theorems/87d65b90-57f3-4865-928a-13479db56411
-- title:
--   HW: weyl Sum split
-- statement:
--   The HW construction uses the weyl Sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L29-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylSum_split {n : ℕ} (ε : Fin n → Bool) (f : Fin n → ℝ) :
    ∑ s, f s = ∑ s ∈ univ.filter (fun s => ε s = true), f s +
      ∑ s ∈ univ.filter (fun s => ε s = false), f s := by sorry
