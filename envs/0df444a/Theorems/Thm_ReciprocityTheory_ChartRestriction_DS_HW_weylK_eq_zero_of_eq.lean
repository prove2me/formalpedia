-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_eq_zero_of_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylK_eq_zero_of_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:28.279458+00:00
-- url     : https://prove2.me/theorems/983fe6ed-e329-4a4a-afa7-48759a1f2d55
-- title:
--   HW: weyl K eq zero of eq
-- statement:
--   The HW construction uses the weyl K eq zero of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylVanish.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylVanish.lean#L13-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylK_eq_zero_of_eq (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b)
    (h : (μ + rhoC ε) a = (μ + rhoC ε) b) : weylK ε μ = 0 := by sorry
