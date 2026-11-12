-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_rz_q_factor_zero
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.rz_q_factor_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:54:39.976947+00:00
-- url     : https://prove2.me/theorems/e8f84287-10c5-4372-9e1a-29b522e1eaa7
-- title:
--   BDL26 Connected Syndrome Mass: rz q factor zero
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the rz q factor zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L308-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L308-L312

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u

theorem QEC.Coding.BDL26ConnectedSyndromeMass.rz_q_factor_zero (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (q : (state S (n+1)).presentation.Q) (t : ℝ) :
    factor S (n+2) (Vertex.q q) t=0 := by sorry
