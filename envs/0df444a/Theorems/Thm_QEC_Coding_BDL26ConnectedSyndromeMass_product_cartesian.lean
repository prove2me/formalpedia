-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_product_cartesian
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.product_cartesian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:11:52.020125+00:00
-- url     : https://prove2.me/theorems/009f6e9d-ee69-4ff9-b1ce-5ab682188597
-- title:
--   BDL26 Connected Syndrome Mass: product cartesian
-- statement:
--   Finite Cartesian distributivity on dependent full original-carrier words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L315-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L315-L334

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.product_cartesian (S : OddScale) (depth : ℕ)
    (T : Finset (decodingGraph S depth).Node) (t : ℝ) :
    (∏ v ∈ T, factor S v.1.val v.2 t) =
      ∑ x : (∀ v : T, {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0}),
        Real.exp (-t*(∑ v : T,
          (HammingWeight (extend S v.val.1.val v.val.2 (x v).val) : ℝ))) := by sorry
