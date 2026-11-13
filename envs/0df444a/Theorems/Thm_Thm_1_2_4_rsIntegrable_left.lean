-- Prove2me | Theorems.Thm_Thm_1_2_4_rsIntegrable_left
-- name    : Thm_1_2_4.rsIntegrable_left
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:11:45.208078+00:00
-- url     : https://prove2.me/theorems/edc7e18c-4449-4aac-8517-7d813a9d29f2
-- title:
--   ProbabilityTheory_chapter_01_thm_1_2_4_F002: Thm_1_2_4.rsIntegrable_left
-- statement:
--   Source theorem `Thm_1_2_4.rsIntegrable_left` from `ProbabilityTheory.chapter_01.thm_1_2_4`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Mathlib.Tactic
noncomputable section Thm_1_2_4
namespace Thm_1_2_4
open scoped BigOperators Pointwise
noncomputable section SubintervalIntegrability

theorem rsIntegrable_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α a c := by
  sorry
end SubintervalIntegrability
end Thm_1_2_4
end Thm_1_2_4
