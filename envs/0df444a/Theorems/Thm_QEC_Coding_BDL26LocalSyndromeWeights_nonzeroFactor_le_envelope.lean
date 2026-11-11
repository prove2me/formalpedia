-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_nonzeroFactor_le_envelope
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_le_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:09:10.395105+00:00
-- url     : https://prove2.me/theorems/f8fa7d44-c08d-4871-aa40-040812e8301d
-- title:
--   BDL26 Local Syndrome Weights: nonzero Factor le envelope
-- statement:
--   The size envelope is an upper bound, never an equality of measured sizes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L162-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L162-L167

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.nonzeroFactor_le_envelope (I : Type*) [Fintype I]
    (t : ℝ) (M : ℕ) (hM : Fintype.card I ≤ M) :
    nonzeroFactor I t ≤ (1 + Real.exp (-t)) ^ M - 1 := by sorry
