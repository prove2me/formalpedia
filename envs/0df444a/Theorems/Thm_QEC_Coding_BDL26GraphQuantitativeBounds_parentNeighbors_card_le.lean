-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_parentNeighbors_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.parentNeighbors_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:57:27.076412+00:00
-- url     : https://prove2.me/theorems/128e1b47-683d-48a9-98d8-f0258011ba84
-- title:
--   BDL26 Graph Quantitative Bounds: parent Neighbors card le
-- statement:
--   The incoming inter-level degree is at most one, including unowned connectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L107-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L107-L111

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.parentNeighbors_card_le (S : OddScale) (n : Nat) (v : GraphVertex S (n+1)) :
    Fintype.card {u : GraphVertex S n // v ∈ localRegion S n u} ≤ 1 := by sorry
