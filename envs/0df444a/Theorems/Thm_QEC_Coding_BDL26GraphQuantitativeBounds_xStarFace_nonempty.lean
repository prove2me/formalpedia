-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarFace_nonempty
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.xStarFace_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:57:52.139195+00:00
-- url     : https://prove2.me/theorems/b7a4f064-21a9-44ab-a25d-73b7cfbea195
-- title:
--   BDL26 Graph Quantitative Bounds: x Star Face nonempty
-- statement:
--   An admissible star has a face: its stored boundary root belongs to a face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L157-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L157-L167

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical

theorem QEC.Coding.BDL26GraphQuantitativeBounds.xStarFace_nonempty (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) : Nonempty (XStarFace P x) := by sorry
