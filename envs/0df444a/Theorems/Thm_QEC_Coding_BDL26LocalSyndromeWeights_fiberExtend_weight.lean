-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_weight
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:25:30.26059+00:00
-- url     : https://prove2.me/theorems/91ad18b1-f9a8-4efe-9d8b-4dbb82c4fa8d
-- title:
--   BDL26 Local Syndrome Weights: fiber Extend weight
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the fiber Extend weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L229-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L229-L237

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_weight {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label) (x : Word Bit {c : C // owner c = label}) :
    HammingWeight (fiberExtend owner label x) = HammingWeight x := by sorry
