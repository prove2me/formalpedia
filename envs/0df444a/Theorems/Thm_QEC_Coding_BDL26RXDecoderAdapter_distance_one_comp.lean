-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_distance_one_comp
-- name    : QEC.Coding.BDL26RXDecoderAdapter.distance_one_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:55:20.200555+00:00
-- url     : https://prove2.me/theorems/3a0c6494-4a9a-4b1f-9734-b5dba6f3004c
-- title:
--   BDL26 RXDecoder Adapter: distance one comp
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the distance one comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L49-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L49-L70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.distance_one_comp {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u v w : V)
    (huv : G.distance u v ≤ (1 : WithTop Nat))
    (hvw : G.distance v w ≤ (1 : WithTop Nat)) :
    G.distance u w ≤ (2 : WithTop Nat) := by sorry
