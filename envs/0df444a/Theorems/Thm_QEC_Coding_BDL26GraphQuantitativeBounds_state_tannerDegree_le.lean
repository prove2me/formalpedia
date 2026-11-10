-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_state_tannerDegree_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.state_tannerDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:23:46.647115+00:00
-- url     : https://prove2.me/theorems/19d5df6e-af3f-4e8d-8b72-b1d37b9e3288
-- title:
--   BDL26 Graph Quantitative Bounds: state tanner Degree le
-- statement:
--   The actual recursive Tanner graph has a scale- and depth-independent bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L85-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L85-L87

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

theorem QEC.Coding.BDL26GraphQuantitativeBounds.state_tannerDegree_le (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : tannerDegree (state S n).presentation v ≤ 7 := by sorry
