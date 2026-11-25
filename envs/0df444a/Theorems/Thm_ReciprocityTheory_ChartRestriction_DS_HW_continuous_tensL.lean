-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_tensL
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.continuous_tensL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:02.604957+00:00
-- url     : https://prove2.me/theorems/e3c094ea-fa23-5c92-91eb-c5da883335ea
-- title:
--   HW: continuous tens L
-- statement:
--   The HW construction uses the continuous tens L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L72-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.DS.HW.continuous_tensL {X : Type*} [TopologicalSpace X] {m : X → Matrix ι ι ℂ} {S : X → V →L[ℂ] V}
    (hm : Continuous m) (hS : Continuous S) : Continuous fun x => tensL (m x) (S x) := by sorry
