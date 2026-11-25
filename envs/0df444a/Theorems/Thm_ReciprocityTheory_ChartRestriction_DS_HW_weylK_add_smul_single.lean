-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_add_smul_single
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.weylK_add_smul_single
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:56.025919+00:00
-- url     : https://prove2.me/theorems/3424598a-ed55-43de-becc-82a85f251bdc
-- title:
--   HW: weyl K add smul single
-- statement:
--   The HW construction uses the weyl K add smul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylRatio.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/WeylRatio.lean#L124-L133

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.weylK_add_smul_single {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n)
    (c : ℝ) :
    weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = weylK ε Λ *
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) := by sorry
