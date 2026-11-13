-- Prove2me | Theorems.Thm_Thm61Support_ereal_mul_finset_sum_of_nonneg_of_ne_top
-- name    : Thm61Support.ereal_mul_finset_sum_of_nonneg_of_ne_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:24:51.933074+00:00
-- url     : https://prove2.me/theorems/5791b74d-9498-44b7-8afd-8ea41ec8140e
-- title:
--   ProbabilityTheory_chapter_06_thm_6_1_F000: Thm61Support.ereal_mul_finset_sum_of_nonneg_of_ne_top
-- statement:
--   Source theorem `Thm61Support.ereal_mul_finset_sum_of_nonneg_of_ne_top` from `ProbabilityTheory.chapter_06.thm_6_1`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]
namespace Thm61Support

theorem ereal_mul_finset_sum_of_nonneg_of_ne_top {ι : Type*} (s : Finset ι)
    {a : EReal} (ha : 0 ≤ a) (ha_top : a ≠ ⊤) (f : ι → EReal) :
    a * (Finset.sum s f) = Finset.sum s (fun i => a * f i) := by
  sorry
end Thm61Support
