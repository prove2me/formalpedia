-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_tensL
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hasDerivAt_tensL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:56.080055+00:00
-- url     : https://prove2.me/theorems/2909d1b3-7253-4bea-84b7-0f6e31e3dd5e
-- title:
--   HW: has Deriv At tens L
-- statement:
--   The HW construction uses the has Deriv At tens L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L78-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L78-L98

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.hasDerivAt_tensL {m : ℝ → Matrix ι ι ℂ} {m' : Matrix ι ι ℂ} {S : ℝ → V →L[ℂ] V}
    {S' : V →L[ℂ] V} {t₀ : ℝ} (hm : ∀ i j, HasDerivAt (fun t => m t i j) (m' i j) t₀)
    (hS : HasDerivAt S S' t₀) :
    HasDerivAt (fun t => tensL (m t) (S t)) (tensL m' (S t₀) + tensL (m t₀) S') t₀ := by sorry
