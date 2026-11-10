-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_nextParentFiber_bound
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.nextParentFiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:59:50.979198+00:00
-- url     : https://prove2.me/theorems/6f4d1dce-6480-4d41-9c4c-22e3532f5f73
-- title:
--   BDL26 Graph Quantitative Bounds: next Parent Fiber bound
-- statement:
--   Parity selection preserves the actual parent-fiber bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L382-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L382-L417

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.nextParentFiber_bound (S : OddScale) (n : Nat) (C : ConstructionState)
    (hC : BoundedValence C.presentation) (u : Vertex C.presentation) :
    Fintype.card {v : Vertex (nextState S n C).presentation //
      nextParent S n C v = some u} ≤ localCoordinateBound S := by sorry
