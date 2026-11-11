-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rz_extend_weight
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.rz_extend_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:09:32.652206+00:00
-- url     : https://prove2.me/theorems/e0b67cfb-90e3-4522-8566-99f7b9d9a129
-- title:
--   BDL26 Local Syndrome Weights: rz extend weight
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the rz extend weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L287-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L287-L291

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.rz_extend_weight (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (x : Word Bit (RZFiber P S z)) :
    HammingWeight (fiberExtend (rzSyndromeOwner P S) z x) = HammingWeight x := by sorry
