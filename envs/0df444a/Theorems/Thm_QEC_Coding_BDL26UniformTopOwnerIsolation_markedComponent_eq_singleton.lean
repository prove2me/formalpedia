-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedComponent_eq_singleton
-- name    : QEC.Coding.BDL26UniformTopOwnerIsolation.markedComponent_eq_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:16:34.343904+00:00
-- url     : https://prove2.me/theorems/4f35019e-a27d-4240-88d5-f43d6a745b2b
-- title:
--   BDL26 Uniform Top Owner Isolation: marked Component eq singleton
-- statement:
--   The marked component is a singleton, regardless of every lower-level mark.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L97-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean#L97-L104

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedComponent_eq_singleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformTopOwnerIsolation.markedComponent_eq_singleton (S : OddScale) (n : Nat) (M : Finset (Node S n)) (hM : TopMarksAreZ S n M)
    (z : (state S n).presentation.Z)
    (hparent : parent S n (Vertex.z z) = none)
    (ha : topNode S n (.z z) ∈ M) :
    markedComponent S n M ⟨topNode S n (.z z),ha⟩ = {⟨topNode S n (.z z),ha⟩} := by sorry
