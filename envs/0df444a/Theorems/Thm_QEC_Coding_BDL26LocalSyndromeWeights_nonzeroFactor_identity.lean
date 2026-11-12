-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_nonzeroFactor_identity
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:48:09.561692+00:00
-- url     : https://prove2.me/theorems/64090d4e-d90a-4f84-a375-94a8196bc93e
-- title:
--   BDL26 Local Syndrome Weights: nonzero Factor identity
-- statement:
--   Both equalities of the source local-factor identity on arbitrary labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L133-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L133-L138

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_identity (I : Type*) [Fintype I] (t : ℝ) :
    nonzeroFactor I t = binomialFactor (Fintype.card I) t ∧
      binomialFactor (Fintype.card I) t = (1 + Real.exp (-t)) ^ Fintype.card I - 1 := by sorry
