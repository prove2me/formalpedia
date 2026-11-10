-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rzParentFiber_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.rzParentFiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:58:36.656646+00:00
-- url     : https://prove2.me/theorems/c6691518-d9f6-4336-943d-5f380273746b
-- title:
--   BDL26 Graph Quantitative Bounds: rz Parent Fiber card le
-- statement:
--   The unchanged RZ inclusion likewise covers its materialized parent fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L322-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L322-L334

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.rzParentFiber_card_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
      rzParent P A S v = some u} ≤ Fintype.card (RZZeroCell P S u) := by sorry
