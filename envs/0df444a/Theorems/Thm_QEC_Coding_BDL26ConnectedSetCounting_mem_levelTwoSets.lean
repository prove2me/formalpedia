-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_mem_levelTwoSets
-- name    : QEC.Coding.BDL26ConnectedSetCounting.mem_levelTwoSets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:44:50.055812+00:00
-- url     : https://prove2.me/theorems/ce17c7df-4d63-4197-af24-e6cd7b1cd6c3
-- title:
--   BDL26 Connected Set Counting: mem level Two Sets
-- statement:
--   The induced connectivity is taken on the complete supplied vertex set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L86-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L86-L91

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

theorem QEC.Coding.BDL26ConnectedSetCounting.mem_levelTwoSets (S : OddScale) (depth m : Nat)
    (A : Finset (decodingGraph S depth).Node) :
    A ∈ levelTwoSets S depth m ↔ A.card = m ∧
      ((graph S depth).induce (A : Set (decodingGraph S depth).Node)).Connected ∧
      (A ∩ levelTwoAnchors S depth).Nonempty := by sorry
