-- Prove2me | Theorems.Thm_Thm61Support_neg_finset_sum_of_forall_ne_top
-- name    : Thm61Support.neg_finset_sum_of_forall_ne_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:25:42.937092+00:00
-- url     : https://prove2.me/theorems/122eef8d-c8d4-46c5-a7a4-d325ea9e0250
-- title:
--   ProbabilityTheory_chapter_06_thm_6_1_F000: Thm61Support.neg_finset_sum_of_forall_ne_top
-- statement:
--   Source theorem `Thm61Support.neg_finset_sum_of_forall_ne_top` from `ProbabilityTheory.chapter_06.thm_6_1`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]
namespace Thm61Support

theorem neg_finset_sum_of_forall_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    Finset.sum s (fun i => -(f i)) = -(Finset.sum s f) := by
  sorry
end Thm61Support
