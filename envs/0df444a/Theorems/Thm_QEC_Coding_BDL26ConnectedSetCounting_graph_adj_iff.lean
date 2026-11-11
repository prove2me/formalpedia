-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_graph_adj_iff
-- name    : QEC.Coding.BDL26ConnectedSetCounting.graph_adj_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:44:39.933415+00:00
-- url     : https://prove2.me/theorems/8ecdb900-64eb-4f2b-8c01-e3a5f9f8384b
-- title:
--   BDL26 Connected Set Counting: graph adj iff
-- statement:
--   The BDL26 Connected Set Counting construction uses the graph adj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L56-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L56-L57

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

theorem QEC.Coding.BDL26ConnectedSetCounting.graph_adj_iff (S : OddScale) (depth : Nat) (u v : (decodingGraph S depth).Node) :
    (graph S depth).Adj u v ↔ (decodingGraph S depth).adjacent u v := by sorry
