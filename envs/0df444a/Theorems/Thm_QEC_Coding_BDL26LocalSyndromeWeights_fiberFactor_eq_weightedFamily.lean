-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberFactor_eq_weightedFamily
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.fiberFactor_eq_weightedFamily
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:37:00.60596+00:00
-- url     : https://prove2.me/theorems/2e11410a-3664-4743-8b0e-0e9c715c326b
-- title:
--   BDL26 Local Syndrome Weights: fiber Factor eq weighted Family
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the fiber Factor eq weighted Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L244-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L244-L251

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.fiberFactor_eq_weightedFamily {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label)
    (A : Finset (Word Bit {c : C // owner c = label})) (t : ℝ) :
    fiberFactor owner label A t = weightedFamily A t := by sorry
