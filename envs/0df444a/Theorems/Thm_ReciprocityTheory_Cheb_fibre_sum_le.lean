-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_fibre_sum_le
-- name    : ReciprocityTheory.Cheb.fibre_sum_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:45.435667+00:00
-- url     : https://prove2.me/theorems/cf1a44f9-2611-5a16-a8db-9e1ad11ced38
-- title:
--   Cheb: fibre sum le
-- statement:
--   The Cheb construction uses the fibre sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitF.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitF.lean#L7-L33

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

theorem ReciprocityTheory.Cheb.fibre_sum_le {α β : Type*} (π : α → β) (f : α → ℝ) (h : β → ℝ) (n : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hfh : ∀ a, f a ≤ h (π a)) (hh0 : ∀ b, 0 ≤ h b) (hh : Summable h)
    (hfib : ∀ b, {a | π a = b}.Finite ∧ {a | π a = b}.ncard ≤ n) :
    Summable f ∧ ∑' a, f a ≤ n * ∑' b, h b := by sorry
