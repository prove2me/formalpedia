-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_compare_cost
-- name    : QEC.Coding.BDL26NativeTriangleKeys.compare_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:55:55.091321+00:00
-- url     : https://prove2.me/theorems/7aab4ea5-69c8-4b3a-b5b2-dd5ad4e7ecb8
-- title:
--   BDL26 Native Triangle Keys: compare cost
-- statement:
--   The BDL26 Native Triangle Keys construction uses the compare cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L491-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L491-L501

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.compare_cost (S : OddScale) (n : ℕ) (a b : Code) :
    operations (compareCodesQ S n a b)≤
        2*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220)+
          106*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+16 ∧
      allocations (compareCodesQ S n a b)≤
        2*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220)+
          4*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+7 := by sorry
