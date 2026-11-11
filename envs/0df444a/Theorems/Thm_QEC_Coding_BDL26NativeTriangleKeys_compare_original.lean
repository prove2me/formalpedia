-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_compare_original
-- name    : QEC.Coding.BDL26NativeTriangleKeys.compare_original
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:38:31.439195+00:00
-- url     : https://prove2.me/theorems/5003bc4a-ae6e-420f-b08b-dc23e8e8baee
-- title:
--   BDL26 Native Triangle Keys: compare original
-- statement:
--   The BDL26 Native Triangle Keys construction uses the compare original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L453-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L453-L456

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.compare_original (S : OddScale) (n : ℕ) (a b : Triangle (P S n)) :
    (compareCodesQ S n (encode S n a) (encode S n b)).1=
      some (decide (nativeLE S n a b)) := by sorry
