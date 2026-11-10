-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_mem_levelTwoAnchors
-- name    : QEC.Coding.BDL26ConnectedSetCounting.mem_levelTwoAnchors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:41:11.64206+00:00
-- url     : https://prove2.me/theorems/98884a51-e949-4441-9b20-166a01b77e93
-- title:
--   BDL26 Connected Set Counting: mem level Two Anchors
-- statement:
--   The BDL26 Connected Set Counting construction uses the mem level Two Anchors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L80-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L80-L83

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

theorem QEC.Coding.BDL26ConnectedSetCounting.mem_levelTwoAnchors (S : OddScale) (depth : Nat) (v : (decodingGraph S depth).Node) :
    v ∈ levelTwoAnchors S depth ↔ v.1.val = 2 := by sorry
