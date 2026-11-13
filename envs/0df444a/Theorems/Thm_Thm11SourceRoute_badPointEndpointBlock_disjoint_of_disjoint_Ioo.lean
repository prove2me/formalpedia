-- Prove2me | Theorems.Thm_Thm11SourceRoute_badPointEndpointBlock_disjoint_of_disjoint_Ioo
-- name    : Thm11SourceRoute.badPointEndpointBlock_disjoint_of_disjoint_Ioo
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:14:27.894512+00:00
-- url     : https://prove2.me/theorems/45aade63-02cb-4209-8249-2928ebb3a31f
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.badPointEndpointBlock_disjoint_of_disjoint_Ioo
-- statement:
--   Source theorem `Thm11SourceRoute.badPointEndpointBlock_disjoint_of_disjoint_Ioo` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem badPointEndpointBlock_disjoint_of_disjoint_Ioo {a b c d r s : ℝ}
    (P : Partition a b)
    (hsep :
      Disjoint (Set.Ioo (c - r) (c + r)) (Set.Ioo (d - s) (d + s))) :
    Disjoint (badPointEndpointBlock P c r) (badPointEndpointBlock P d s) := by sorry

end Thm11SourceRoute
