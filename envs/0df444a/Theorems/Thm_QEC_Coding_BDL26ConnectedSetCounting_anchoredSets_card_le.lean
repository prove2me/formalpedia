-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_anchoredSets_card_le
-- name    : QEC.Coding.BDL26ConnectedSetCounting.anchoredSets_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:08:43.626071+00:00
-- url     : https://prove2.me/theorems/c3ef5658-6ff1-4543-a712-15c04e5aca00
-- title:
--   BDL26 Connected Set Counting: anchored Sets card le
-- statement:
--   The BDL26 Connected Set Counting construction uses the anchored Sets card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L100-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSetCounting.lean#L100-L105

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds

theorem QEC.Coding.BDL26ConnectedSetCounting.anchoredSets_card_le (S : OddScale) (depth : Nat)
    (R : Finset (decodingGraph S depth).Node) (m : Nat) :
    (anchoredSets S depth R m).card ≤ R.card * (14*S.ell^2+9)^(2*m) := by sorry
