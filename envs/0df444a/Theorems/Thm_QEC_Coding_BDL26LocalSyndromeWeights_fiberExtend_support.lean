-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_support
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:09:54.179341+00:00
-- url     : https://prove2.me/theorems/5abd1a16-57f7-4c3a-9ccc-995e6a4eccaf
-- title:
--   BDL26 Local Syndrome Weights: fiber Extend support
-- statement:
--   Full support image in the actual carrier, including every geometric copy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L208-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L208-L227

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical

theorem QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_support {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label) (x : Word Bit {c : C // owner c = label}) :
    hammingSupport (fiberExtend owner label x) =
      (hammingSupport x).image Subtype.val := by sorry
