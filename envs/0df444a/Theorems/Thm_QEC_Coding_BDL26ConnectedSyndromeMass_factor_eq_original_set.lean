-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_factor_eq_original_set
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.factor_eq_original_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:52:56.940195+00:00
-- url     : https://prove2.me/theorems/2092aa86-f794-4e6e-b8c2-53bf200aa980
-- title:
--   BDL26 Connected Syndrome Mass: factor eq original set
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the factor eq original set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L86-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L86-L88

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.factor_eq_original_set (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) :
    factor S i u t = weightedFamily ((localWords S i u).image (extend S i u)) t := by sorry
