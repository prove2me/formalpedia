-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_shift
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylSum_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:33.918804+00:00
-- url     : https://prove2.me/theorems/bf78d89c-09e8-4a3c-ae19-e0b32109caf1
-- title:
--   HW: weyl Sum shift
-- statement:
--   The HW construction uses the weyl Sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L56-L63

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylSum_shift {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (c : ℝ)
    (hc : ∀ β : Bool, ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
        ((univ.filter (fun s => ε s = β)).card : ℝ)) :
    ∑ s, weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = (n : ℝ) * weylK ε Λ := by sorry
