-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_apply
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:41:57.515027+00:00
-- url     : https://prove2.me/theorems/85970c08-0c25-48e3-b104-fa79169b28aa
-- title:
--   BDL26 Local Syndrome Weights: fiber Extend apply
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the fiber Extend apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L194-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L194-L196

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_apply {C Label : Type*} (owner : C → Label) (label : Label)
    (x : Word Bit {c : C // owner c = label}) (c : C) (hc : owner c = label) :
    fiberExtend owner label x c = x ⟨c,hc⟩ := by sorry
