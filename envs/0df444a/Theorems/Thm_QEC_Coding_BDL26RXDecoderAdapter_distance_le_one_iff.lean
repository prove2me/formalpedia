-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_distance_le_one_iff
-- name    : QEC.Coding.BDL26RXDecoderAdapter.distance_le_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:12:39.641209+00:00
-- url     : https://prove2.me/theorems/ff257fab-af0a-4e2a-8278-832464ee757f
-- title:
--   BDL26 RXDecoder Adapter: distance le one iff
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the distance le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L39-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L39-L47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.distance_le_one_iff {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u v : V) :
    G.distance u v ≤ (1 : WithTop Nat) ↔ u = v ∨ G.edge u v = true := by sorry
