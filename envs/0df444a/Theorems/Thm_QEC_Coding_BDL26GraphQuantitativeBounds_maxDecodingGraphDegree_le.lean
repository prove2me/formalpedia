-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_maxDecodingGraphDegree_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.maxDecodingGraphDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:51:12.759159+00:00
-- url     : https://prove2.me/theorems/33c389f4-1145-4628-bf38-1f1bf6a68a7e
-- title:
--   BDL26 Graph Quantitative Bounds: max Decoding Graph Degree le
-- statement:
--   The BDL26 Graph Quantitative Bounds construction uses the max Decoding Graph Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L672-L677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L672-L677

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
open BDL26ReplacementSupport

theorem QEC.Coding.BDL26GraphQuantitativeBounds.maxDecodingGraphDegree_le (S : OddScale) (depth : Nat) :
    maxDecodingGraphDegree S depth ≤ fullGraphDegreeBound S := by sorry
