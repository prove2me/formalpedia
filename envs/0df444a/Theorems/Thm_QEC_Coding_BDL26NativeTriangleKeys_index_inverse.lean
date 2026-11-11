-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_index_inverse
-- name    : QEC.Coding.BDL26NativeTriangleKeys.index_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:18:29.680205+00:00
-- url     : https://prove2.me/theorems/68dbc5fa-6d65-468c-9f6a-7d32eef3a17e
-- title:
--   BDL26 Native Triangle Keys: index inverse
-- statement:
--   The BDL26 Native Triangle Keys construction uses the index inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L305-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L305-L308

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.index_inverse (S : OddScale) (n : ℕ) :
    (∀t,(nativeTriangleIndex S n).symm (nativeTriangleIndex S n t)=t) ∧
      (∀k,nativeTriangleIndex S n ((nativeTriangleIndex S n).symm k)=k) := by sorry
