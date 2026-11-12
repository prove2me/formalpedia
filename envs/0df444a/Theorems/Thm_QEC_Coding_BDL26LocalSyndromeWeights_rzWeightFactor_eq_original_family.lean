-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rzWeightFactor_eq_original_family
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.rzWeightFactor_eq_original_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:52:43.07099+00:00
-- url     : https://prove2.me/theorems/0371ec8b-cbc4-4f2b-b1ec-71f4fac000d2
-- title:
--   BDL26 Local Syndrome Weights: rz Weight Factor eq original family
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the rz Weight Factor eq original family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L303-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L303-L307

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.rzWeightFactor_eq_original_family (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (A : Finset (Word Bit (RZFiber P S z))) (t : ℝ) :
    rzWeightFactor P S z A t =
      weightedFamily (A.image (fiberExtend (rzSyndromeOwner P S) z)) t := by sorry
