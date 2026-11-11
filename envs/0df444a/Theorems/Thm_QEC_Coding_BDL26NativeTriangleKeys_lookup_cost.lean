-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_cost
-- name    : QEC.Coding.BDL26NativeTriangleKeys.lookup_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:48:26.648908+00:00
-- url     : https://prove2.me/theorems/d8d4f5e7-dc0f-423b-956a-b9084d63884a
-- title:
--   BDL26 Native Triangle Keys: lookup cost
-- statement:
--   The BDL26 Native Triangle Keys construction uses the lookup cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L91-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L91-L101

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.lookup_cost (c : Code) (rs : List KeyRow) :
    operations (lookupRowsQ c rs)≤43*rs.length+1 ∧
      allocations (lookupRowsQ c rs)≤1 := by sorry
