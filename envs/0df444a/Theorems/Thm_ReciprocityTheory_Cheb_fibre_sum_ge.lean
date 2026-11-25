-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_fibre_sum_ge
-- name    : ReciprocityTheory.Cheb.fibre_sum_ge
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:12.887893+00:00
-- url     : https://prove2.me/theorems/8f48b04c-4703-4452-a09c-675ba6458050
-- title:
--   Cheb: fibre sum ge
-- statement:
--   The Cheb construction uses the fibre sum ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitF.lean#L35-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitF.lean#L35-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.fibre_sum_ge {α β : Type*} (π : α → β) (f : α → ℝ) (g : β → ℝ) (k : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hf : Summable f) (hg0 : ∀ b, 0 ≤ g b) (hg : Summable g) (S : Set β) (hS : S.Finite)
    (hfib : ∀ b ∉ S, k ≤ {a | π a = b ∧ f a = g b}.ncard) :
    (k : ℝ) * ∑' b, g b ≤ ∑' a, f a + k * ∑' b, S.indicator g b := by sorry
