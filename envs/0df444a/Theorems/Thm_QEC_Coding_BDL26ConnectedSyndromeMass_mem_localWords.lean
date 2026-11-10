-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_mem_localWords
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.mem_localWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:42:20.590192+00:00
-- url     : https://prove2.me/theorems/1c77f421-5563-4191-8cc8-f2b89ebb6754
-- title:
--   BDL26 Connected Syndrome Mass: mem local Words
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the mem local Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L78-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L78-L80

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.mem_localWords (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (x : Word Bit (OwnerFiber S i u)) : x∈localWords S i u ↔ x≠0 := by sorry
