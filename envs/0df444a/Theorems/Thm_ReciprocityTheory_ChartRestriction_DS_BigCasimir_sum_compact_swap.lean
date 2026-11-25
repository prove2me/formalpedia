-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_sum_compact_swap
-- name    : ReciprocityTheory.ChartRestriction.DS.BigCasimir.sum_compact_swap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:50.93087+00:00
-- url     : https://prove2.me/theorems/2f81dd44-c320-4a5e-a923-a7b406b82093
-- title:
--   Big Casimir: sum compact swap
-- statement:
--   The Big Casimir construction uses the sum compact swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L17-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.BigCasimir.sum_compact_swap {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f a b =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f b a := by sorry
