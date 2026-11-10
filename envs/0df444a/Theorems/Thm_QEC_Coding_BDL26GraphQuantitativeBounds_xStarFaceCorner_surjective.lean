-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarFaceCorner_surjective
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.xStarFaceCorner_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:58:06.44948+00:00
-- url     : https://prove2.me/theorems/e558f8b0-8558-4df4-8d34-363e755d7bef
-- title:
--   BDL26 Graph Quantitative Bounds: x Star Face Corner surjective
-- statement:
--   Actual face corners cover the constructed local-star vertex carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L170-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L170-L197

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.xStarFaceCorner_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) :
    Function.Surjective (fun fc : XStarFace P x ×
      (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) =>
        xStarFaceCorner P x fc.1 fc.2) := by sorry
