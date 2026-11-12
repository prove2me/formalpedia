-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_compare_failure
-- name    : QEC.Coding.BDL26NativeTriangleKeys.compare_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:39:38.797389+00:00
-- url     : https://prove2.me/theorems/94bb990a-3f6a-4751-8847-4d48520e9f22
-- title:
--   BDL26 Native Triangle Keys: compare failure
-- statement:
--   The BDL26 Native Triangle Keys construction uses the compare failure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L458-L462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L458-L462

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.compare_failure (S : OddScale) (n : ℕ) (a b : Code) :
    (compareCodesQ S n a b).1=none ↔
      (keyOfCodeQ S n a).1=none ∨ (keyOfCodeQ S n b).1=none := by sorry
