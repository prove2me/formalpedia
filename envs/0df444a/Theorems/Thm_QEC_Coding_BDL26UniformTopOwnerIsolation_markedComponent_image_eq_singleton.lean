-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedComponent_image_eq_singleton
-- name    : QEC.Coding.BDL26UniformTopOwnerIsolation.markedComponent_image_eq_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:44:05.445008+00:00
-- url     : https://prove2.me/theorems/fe4515c9-b8d6-4513-ace6-d64a3b1c8a85
-- title:
--   BDL26 Uniform Top Owner Isolation: marked Component image eq singleton
-- statement:
--   The same component has exactly the one underlying node in the original (graph S n).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L107-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L107-L113

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedComponent_image_eq_singleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformTopOwnerIsolation.markedComponent_image_eq_singleton (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) :
    (markedComponent S n M ⟨topNode S n (.z z),ha⟩).image Subtype.val = {topNode S n (.z z)} := by sorry
