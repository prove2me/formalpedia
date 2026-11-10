-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedComponent_image_eq_singleton
-- name    : QEC.Coding.BDL26TopOwnerIsolation.markedComponent_image_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:13:54.920564+00:00
-- url     : https://prove2.me/theorems/64631a71-c3e0-4247-868c-0864a62f332f
-- title:
--   BDL26 Top Owner Isolation: marked Component image eq singleton
-- statement:
--   The same component has exactly the one underlying node in the original graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L113-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L113-L119

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26TopOwnerIsolation.markedComponent_image_eq_singleton (M : Finset Node) (hM : TopMarksAreZ M)
    (z : (state scaleFive 3).presentation.Z)
    (hparent : parent scaleFive 3 (Vertex.z z) = none)
    (ha : topNode (.z z) ∈ M) :
    (markedComponent M ⟨topNode (.z z),ha⟩).image Subtype.val = {topNode (.z z)} := by sorry
