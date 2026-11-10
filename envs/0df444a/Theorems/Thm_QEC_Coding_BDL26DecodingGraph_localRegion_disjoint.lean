-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_localRegion_disjoint
-- name    : QEC.Coding.BDL26DecodingGraph.localRegion_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:02:03.37921+00:00
-- url     : https://prove2.me/theorems/2bb4f1af-c967-47ed-854c-3aac87a8e0fb
-- title:
--   BDL26 Decoding Graph: local Region disjoint
-- statement:
--   Local zero-cell regions are disjoint because their concrete tags determine the parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L324-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L324-L331

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.localRegion_disjoint (S : OddScale) (n : Nat)
    (u w : GraphVertex S n) (hne : u ≠ w) :
    Disjoint (localRegion S n u) (localRegion S n w) := by sorry
