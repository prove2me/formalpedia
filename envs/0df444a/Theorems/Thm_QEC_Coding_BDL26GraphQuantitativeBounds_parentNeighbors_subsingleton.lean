-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_parentNeighbors_subsingleton
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.parentNeighbors_subsingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:57:41.393196+00:00
-- url     : https://prove2.me/theorems/c89f1204-293c-4352-8de2-65f2fc784e47
-- title:
--   BDL26 Graph Quantitative Bounds: parent Neighbors subsingleton
-- statement:
--   At most one lower neighbor can be incident to any upper graph vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L96-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L96-L104

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.parentNeighbors_subsingleton (S : OddScale) (n : Nat)
    (v : GraphVertex S (n+1)) :
    Subsingleton {u : GraphVertex S n // v ∈ localRegion S n u} := by sorry
