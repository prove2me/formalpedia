-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_no_marked_neighbor
-- name    : QEC.Coding.BDL26TopOwnerIsolation.no_marked_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:18:07.60145+00:00
-- url     : https://prove2.me/theorems/cbdb43e8-b780-4aec-b166-5db850c23661
-- title:
--   BDL26 Top Owner Isolation: no marked neighbor
-- statement:
--   A top Z node with no intrinsic parent cannot have any marked neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L39-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L39-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26TopOwnerIsolation.no_marked_neighbor (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (w : Node) (hw : w ∈ M) :
    ¬ graph.adjacent (topNode (.z z)) w := by sorry
