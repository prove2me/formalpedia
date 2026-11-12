-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_marked_path_iff_eq
-- name    : QEC.Coding.BDL26UniformTopOwnerIsolation.marked_path_iff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:16:32.191758+00:00
-- url     : https://prove2.me/theorems/a625165d-0f77-4c85-9f1a-f5bc5715c87e
-- title:
--   BDL26 Uniform Top Owner Isolation: marked path iff eq
-- statement:
--   Reachability in the actual induced marked graph reduces to equality at this node.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L77-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L77-L89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_marked_path_iff_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformTopOwnerIsolation.marked_path_iff_eq (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) (w : {w : Node S n // w ∈ M}) :
    Relation.ReflTransGen (markedAdjacent S n M) ⟨topNode S n (.z z),ha⟩ w ↔
      w = ⟨topNode S n (.z z),ha⟩ := by sorry
