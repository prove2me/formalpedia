-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_failure
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:47:39.098197+00:00
-- url     : https://prove2.me/theorems/db0fba01-85ff-4d9e-aa78-cba80afa6b78
-- title:
--   BDL26 Native Triangle Keys: key Of Code failure
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Of Code failure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L395-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L395-L406

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_failure (S : OddScale) (n : ℕ) (c : Code) :
    (keyOfCodeQ S n c).1=none ↔
      ¬∃t : Triangle (P S n),encode S n t=c := by sorry
