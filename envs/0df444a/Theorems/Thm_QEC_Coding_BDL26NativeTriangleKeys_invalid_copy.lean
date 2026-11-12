-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_invalid_copy
-- name    : QEC.Coding.BDL26NativeTriangleKeys.invalid_copy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:37:48.160209+00:00
-- url     : https://prove2.me/theorems/e8ad896e-b55a-48de-9be5-1a13c0a78583
-- title:
--   BDL26 Native Triangle Keys: invalid copy
-- statement:
--   The BDL26 Native Triangle Keys construction uses the invalid copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L421-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L421-L428

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.invalid_copy (S : OddScale) (n : ℕ) (c : Code) (h : 2≤c.copy) :
    (keyOfCodeQ S n c).1=none := by sorry
