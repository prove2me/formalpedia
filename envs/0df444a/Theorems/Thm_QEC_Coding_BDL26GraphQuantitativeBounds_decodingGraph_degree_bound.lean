-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_decodingGraph_degree_bound
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.decodingGraph_degree_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:40:01.224693+00:00
-- url     : https://prove2.me/theorems/c93aff1c-7ab6-4648-a03d-9b346d868e0a
-- title:
--   BDL26 Graph Quantitative Bounds: decoding Graph degree bound
-- statement:
--   Every actual truncation satisfies the same finite degree envelope.
--   The singleton root and top truncation are included in the finite witness cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L543-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L543-L571

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.decodingGraph_degree_bound (S : OddScale) (depth : Nat)
    (u : (decodingGraph S depth).Node) :
    Nat.card {v : (decodingGraph S depth).Node //
      (decodingGraph S depth).adjacent u v} ≤ fullGraphDegreeBound S := by sorry
