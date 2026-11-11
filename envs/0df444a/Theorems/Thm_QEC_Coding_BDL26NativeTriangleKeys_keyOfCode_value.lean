-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_value
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:51:04.55281+00:00
-- url     : https://prove2.me/theorems/d2c1aae8-2ade-4543-a79a-d5ca3f914d29
-- title:
--   BDL26 Native Triangle Keys: key Of Code value
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Of Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L368-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L368-L371

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_value (S : OddScale) (n : ℕ) (c : Code) :
    (keyOfCodeQ S n c).1=
      if c∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles then some (2*c.owner+c.copy) else none := by sorry
