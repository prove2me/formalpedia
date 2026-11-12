-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_success
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:36:18.949303+00:00
-- url     : https://prove2.me/theorems/616342de-4d76-4073-bed2-88fa2a46d965
-- title:
--   BDL26 Native Triangle Keys: key Of Code success
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Of Code success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L378-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L378-L393

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_success (S : OddScale) (n : ℕ) (c : Code) (k : ℕ) :
    (keyOfCodeQ S n c).1=some k ↔
      ∃!t : Triangle (P S n),encode S n t=c ∧ (nativeTriangleIndex S n t).val=k := by sorry
