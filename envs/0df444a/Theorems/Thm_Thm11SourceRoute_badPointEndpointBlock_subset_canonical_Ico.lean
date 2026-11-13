-- Prove2me | Theorems.Thm_Thm11SourceRoute_badPointEndpointBlock_subset_canonical_Ico
-- name    : Thm11SourceRoute.badPointEndpointBlock_subset_canonical_Ico
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:44:32.269797+00:00
-- url     : https://prove2.me/theorems/712ff961-7b71-4eff-a709-b59e6b69b979
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.badPointEndpointBlock_subset_canonical_Ico
-- statement:
--   Source theorem `Thm11SourceRoute.badPointEndpointBlock_subset_canonical_Ico` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem badPointEndpointBlock_subset_canonical_Ico {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointEndpointBlock P c r ⊆
      Finset.Ico (badPointCanonicalLo P c r) (badPointCanonicalHi P c r) := by sorry

end Thm11SourceRoute
