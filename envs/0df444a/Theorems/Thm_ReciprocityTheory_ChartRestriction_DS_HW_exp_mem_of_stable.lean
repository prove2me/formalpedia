-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exp_mem_of_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.exp_mem_of_stable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:38.313178+00:00
-- url     : https://prove2.me/theorems/a667b126-51da-4ff5-bf6b-55efd78ea2d3
-- title:
--   HW: exp mem of stable
-- statement:
--   The HW construction uses the exp mem of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L49-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.exp_mem_of_stable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ V) (A : V →L[ℂ] V) (hA : ∀ v ∈ W, A v ∈ W) :
    ∀ v ∈ W, NormedSpace.exp A v ∈ W := by sorry
