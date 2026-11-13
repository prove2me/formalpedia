-- Prove2me | Theorems.Thm_Thm_1_2_4_thm_1_4
-- name    : Thm_1_2_4.thm_1_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:57:11.5792+00:00
-- url     : https://prove2.me/theorems/98d3616a-a46a-4df9-b31f-ae66ef44bb3c
-- title:
--   ProbabilityTheory_chapter_01_thm_1_2_4_F004: Thm_1_2_4.thm_1_4
-- statement:
--   Source theorem `Thm_1_2_4.thm_1_4` from `ProbabilityTheory.chapter_01.thm_1_2_4`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F003
import Mathlib.Tactic
noncomputable section Thm_1_2_4
namespace Thm_1_2_4

private theorem rsIntegrable_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α a c :=
  rsIntegrable_left_source hac hcb hab

private theorem rsIntegrable_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α c b :=
  rsIntegrable_right_source hac hcb hab

open scoped BigOperators Pointwise
noncomputable section SubintervalIntegrability
end SubintervalIntegrability

theorem thm_1_4 {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hab : RSIntegrable f α a b) :
    rsIntegral f α a b hab =
      rsIntegral f α a c (rsIntegrable_left hac hcb hab) +
      rsIntegral f α c b (rsIntegrable_right hac hcb hab) := by
  sorry
end Thm_1_2_4
end Thm_1_2_4
