-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_card
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:11:18.208124+00:00
-- url     : https://prove2.me/theorems/33073e74-6a8c-4135-9400-adf778d83c11
-- title:
--   BDL26 Connected Syndrome Mass: owner Fiber card
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the owner Fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L273-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L273-L275

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_card (S : OddScale) (i : ℕ) (u : GraphVertex S i) :
    Fintype.card (OwnerFiber S i u) ≤ 14*S.ell^2 := by sorry
