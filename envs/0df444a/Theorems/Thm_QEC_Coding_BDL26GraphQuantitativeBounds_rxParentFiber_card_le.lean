-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxParentFiber_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.rxParentFiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:58:49.988358+00:00
-- url     : https://prove2.me/theorems/4ec80251-e50f-424d-b690-a82f2ce57398
-- title:
--   BDL26 Graph Quantitative Bounds: rx Parent Fiber card le
-- statement:
--   The unchanged RX inclusion covers exactly the actual parent fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L308-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L308-L319

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.rxParentFiber_card_le (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) :
    Fintype.card {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} ≤ Fintype.card (RXZeroCell P S u) := by sorry
