-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_inj
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylSum_inj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:19:04.556193+00:00
-- url     : https://prove2.me/theorems/a36396e3-702d-4a8f-94f5-ddb710e0129e
-- title:
--   HW: weyl Sum inj
-- statement:
--   The HW construction uses the weyl Sum inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylSum.lean#L15-L27

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylSum_inj {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hΛ : KDom ε Λ) (β : Bool) :
    ∀ a b, ε a = β → ε b = β → (Λ + rhoC ε) a = (Λ + rhoC ε) b → a = b := by sorry
