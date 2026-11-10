-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_binomialFactor_eq_power
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.binomialFactor_eq_power
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:09:25.339234+00:00
-- url     : https://prove2.me/theorems/9e6e6302-8163-4d82-b375-5570632c43b2
-- title:
--   BDL26 Local Syndrome Weights: binomial Factor eq power
-- statement:
--   The binomial sum is precisely the nonconstant part of the power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L111-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L111-L130

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.binomialFactor_eq_power (N : ℕ) (t : ℝ) :
    binomialFactor N t = (1 + Real.exp (-t)) ^ N - 1 := by sorry
