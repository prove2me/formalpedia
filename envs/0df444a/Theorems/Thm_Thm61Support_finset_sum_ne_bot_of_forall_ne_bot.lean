-- Prove2me | Theorems.Thm_Thm61Support_finset_sum_ne_bot_of_forall_ne_bot
-- name    : Thm61Support.finset_sum_ne_bot_of_forall_ne_bot
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:25:30.715209+00:00
-- url     : https://prove2.me/theorems/3ebd833f-1d63-47a6-9aad-ad2e0709f02d
-- title:
--   ProbabilityTheory_chapter_06_thm_6_1_F000: Thm61Support.finset_sum_ne_bot_of_forall_ne_bot
-- statement:
--   Source theorem `Thm61Support.finset_sum_ne_bot_of_forall_ne_bot` from `ProbabilityTheory.chapter_06.thm_6_1`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]
namespace Thm61Support

theorem finset_sum_ne_bot_of_forall_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) :
    Finset.sum s f ≠ ⊥ := by
  sorry
end Thm61Support
