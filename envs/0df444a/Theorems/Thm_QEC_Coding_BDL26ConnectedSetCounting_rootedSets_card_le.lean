-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_rootedSets_card_le
-- name    : QEC.Coding.BDL26ConnectedSetCounting.rootedSets_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:08:01.341627+00:00
-- url     : https://prove2.me/theorems/9ad0d7ff-5555-4d75-be10-2cc2cbf14d8c
-- title:
--   BDL26 Connected Set Counting: rooted Sets card le
-- statement:
--   The BDL26 Connected Set Counting construction uses the rooted Sets card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L93-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L93-L98

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

theorem QEC.Coding.BDL26ConnectedSetCounting.rootedSets_card_le (S : OddScale) (depth : Nat)
    (r : (decodingGraph S depth).Node) (m : Nat) :
    (rootedSets S depth r m).card ≤ (14*S.ell^2+9)^(2*m) := by sorry
