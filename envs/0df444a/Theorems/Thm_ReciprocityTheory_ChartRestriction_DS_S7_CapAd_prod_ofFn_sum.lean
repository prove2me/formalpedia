-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapAd_prod_ofFn_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapAd.prod_ofFn_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:46:46.756396+00:00
-- url     : https://prove2.me/theorems/17c9c2dd-6e38-5879-8bfa-3992274890d3
-- title:
--   Cap Ad: prod of Fn sum
-- statement:
--   The Cap Ad construction uses the prod of Fn sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ProdOfFnSmul.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ProdOfFnSmul.lean#L13-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.CapAd
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapAd.prod_ofFn_sum {α : Type*} [Fintype α] : ∀ {p : ℕ} (f : Fin p → α → 𝒰),
    (List.ofFn fun j => ∑ a, f j a).prod = ∑ γ : Fin p → α, (List.ofFn fun j => f j (γ j)).prod
  := by sorry
