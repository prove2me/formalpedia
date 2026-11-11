-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_atlas_original_row
-- name    : QEC.Coding.BDL26NativeTriangleKeys.atlas_original_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:22:29.700947+00:00
-- url     : https://prove2.me/theorems/c3c377a4-e3c4-404d-875e-3cfb007f4f0d
-- title:
--   BDL26 Native Triangle Keys: atlas original row
-- statement:
--   The BDL26 Native Triangle Keys construction uses the atlas original row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L344-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L344-L348

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.atlas_original_row (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (encode S n t,(nativeTriangleIndex S n t).val)∈(keySetupQ S n).1 := by sorry
