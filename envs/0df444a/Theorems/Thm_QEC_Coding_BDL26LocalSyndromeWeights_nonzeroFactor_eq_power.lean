-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_nonzeroFactor_eq_power
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_eq_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:24:52.530488+00:00
-- url     : https://prove2.me/theorems/5c124a5e-e653-4147-ab89-72c98ac4b879
-- title:
--   BDL26 Local Syndrome Weights: nonzero Factor eq power
-- statement:
--   Exact deletion of the one zero-word contribution, for every real t.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L99-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L99-L108

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_eq_power (I : Type*) [Fintype I] (t : ℝ) :
    nonzeroFactor I t = (1 + Real.exp (-t)) ^ Fintype.card I - 1 := by sorry
