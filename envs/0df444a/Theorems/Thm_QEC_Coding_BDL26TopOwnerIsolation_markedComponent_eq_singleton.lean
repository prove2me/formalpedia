-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedComponent_eq_singleton
-- name    : QEC.Coding.BDL26TopOwnerIsolation.markedComponent_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:18:25.236976+00:00
-- url     : https://prove2.me/theorems/6c4e40b9-5237-4429-a6cc-590ce2df36c0
-- title:
--   BDL26 Top Owner Isolation: marked Component eq singleton
-- statement:
--   The marked component is a singleton, regardless of every lower-level mark.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L103-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L103-L110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26TopOwnerIsolation.markedComponent_eq_singleton (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) :
    markedComponent M ⟨topNode (.z z),ha⟩ = {⟨topNode (.z z),ha⟩} := by sorry
