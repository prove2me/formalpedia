-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_cost
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:17:42.009223+00:00
-- url     : https://prove2.me/theorems/235a08ff-2aa4-4822-b4ad-4a9d5534f71d
-- title:
--   BDL26 Native Triangle Keys: key Of Code cost
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Of Code cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L474-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L474-L489

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_cost (S : OddScale) (n : ℕ) (c : Code) :
    operations (keyOfCodeQ S n c)≤
        (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+53*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+6 ∧
      allocations (keyOfCodeQ S n c)≤
        (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+2*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+3 := by sorry
