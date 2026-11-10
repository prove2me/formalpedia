-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_slice_card
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.slice_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:42:52.025188+00:00
-- url     : https://prove2.me/theorems/c15f5b40-6994-4828-8c2b-dfa08a249287
-- title:
--   BDL26 Connected Syndrome Mass: slice card
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the slice card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L351-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L351-L353

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.slice_card (S : OddScale) (depth : ℕ) (i : LevelIndex depth) :
    (slice S depth i).card = Fintype.card (GraphVertex S i.val) := by sorry
