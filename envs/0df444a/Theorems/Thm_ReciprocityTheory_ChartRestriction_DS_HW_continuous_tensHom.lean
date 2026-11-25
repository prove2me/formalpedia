-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_tensHom
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.continuous_tensHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:34.067795+00:00
-- url     : https://prove2.me/theorems/de82a163-10f5-5502-bc92-b6495886ed70
-- title:
--   HW: continuous tens Hom
-- statement:
--   The HW construction uses the continuous tens Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L109-L113

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
variable {G : Type*} [Monoid G] [CompleteSpace V]

theorem ReciprocityTheory.ChartRestriction.DS.HW.continuous_tensHom [TopologicalSpace G] {ρ : G →* unitary (Matrix ι ι ℂ)}
    {σ : G →* unitary (V →L[ℂ] V)}
    (hρ : Continuous (fun g : G => ((ρ g : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ))) (hσ : Continuous σ) :
    Continuous (tensHom ρ σ) := by sorry
