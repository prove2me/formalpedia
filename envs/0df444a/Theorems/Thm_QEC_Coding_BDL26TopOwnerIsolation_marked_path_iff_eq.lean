-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_marked_path_iff_eq
-- name    : QEC.Coding.BDL26TopOwnerIsolation.marked_path_iff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:18:49.954782+00:00
-- url     : https://prove2.me/theorems/3927d986-391a-40b7-af4c-2b834f6ac512
-- title:
--   BDL26 Top Owner Isolation: marked path iff eq
-- statement:
--   Reachability in the actual induced marked graph reduces to equality at this node.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L83-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L83-L95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26TopOwnerIsolation.marked_path_iff_eq (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) (w : {w : Node // w ∈ M}) :
    Relation.ReflTransGen (markedAdjacent M) ⟨topNode (.z z),ha⟩ w ↔
      w = ⟨topNode (.z z),ha⟩ := by sorry
