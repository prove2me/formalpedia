-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_cartesian
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_cartesian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:08:51.145923+00:00
-- url     : https://prove2.me/theorems/f0d9273b-2e1f-45a2-848c-4514dabe7a42
-- title:
--   BDL26 Connected Syndrome Mass: actual cartesian
-- statement:
--   Complete occupied-owner Cartesian mass, without global syndrome coherence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L443-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L443-L453

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_cartesian (S : OddScale) (depth m : ℕ) (t : ℝ) :
    actualMass S depth m t=
      ∑ K ∈ BDL26ConnectedSetCounting.levelTwoSets S depth m,
        ∑ x : (∀ v : (show Finset (Node S depth) from K \ structural S depth),
          {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0}),
          Real.exp (-t*(∑ v : (show Finset (Node S depth) from K \ structural S depth),
            (HammingWeight (extend S v.val.1.val v.val.2 (x v).val) : ℝ))) := by sorry
