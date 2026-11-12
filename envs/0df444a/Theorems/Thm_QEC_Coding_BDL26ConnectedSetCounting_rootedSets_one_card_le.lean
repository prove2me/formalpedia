-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_rootedSets_one_card_le
-- name    : QEC.Coding.BDL26ConnectedSetCounting.rootedSets_one_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:48:06.34361+00:00
-- url     : https://prove2.me/theorems/e9aff948-8a58-41e7-8c0f-850d08b4687e
-- title:
--   BDL26 Connected Set Counting: rooted Sets one card le
-- statement:
--   The full rooted formula includes m=1 without a nontriviality premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L132-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L132-L135

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

theorem QEC.Coding.BDL26ConnectedSetCounting.rootedSets_one_card_le (S : OddScale) (depth : Nat)
    (r : (decodingGraph S depth).Node) :
    (rootedSets S depth r 1).card ≤ (14*S.ell^2+9)^2 := by sorry
