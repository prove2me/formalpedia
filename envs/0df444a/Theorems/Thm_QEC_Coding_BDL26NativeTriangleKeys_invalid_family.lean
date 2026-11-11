-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_invalid_family
-- name    : QEC.Coding.BDL26NativeTriangleKeys.invalid_family
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:39:55.072661+00:00
-- url     : https://prove2.me/theorems/9348d52e-cc8a-4f3c-b0a8-955eb0af1830
-- title:
--   BDL26 Native Triangle Keys: invalid family
-- statement:
--   The BDL26 Native Triangle Keys construction uses the invalid family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L409-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L409-L413

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.invalid_family (S : OddScale) (n : ℕ) (c : Code) (h : c.family≠3) :
    (keyOfCodeQ S n c).1=none := by sorry
