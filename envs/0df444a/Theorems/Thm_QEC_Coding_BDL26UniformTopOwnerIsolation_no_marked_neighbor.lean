-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_no_marked_neighbor
-- name    : QEC.Coding.BDL26UniformTopOwnerIsolation.no_marked_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:16:21.453376+00:00
-- url     : https://prove2.me/theorems/579dce7d-c105-4813-a3e7-fb894006314c
-- title:
--   BDL26 Uniform Top Owner Isolation: no marked neighbor
-- statement:
--   A top Z node with no intrinsic parent cannot have any marked neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L32-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L32-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_no_marked_neighbor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformTopOwnerIsolation.no_marked_neighbor (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (w : Node S n) (hw : w ∈ M) :
    ¬ (graph S n).adjacent (topNode S n (.z z)) w := by sorry
