-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyRows_spec
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyRows_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:14:49.163331+00:00
-- url     : https://prove2.me/theorems/e07d4713-2cd0-48ed-8591-c9cae6b60937
-- title:
--   BDL26 Native Triangle Keys: key Rows spec
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Rows spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L80-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L80-L89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keyRows_spec (cs : List Code) :
    (keyRowsQ cs).1=cs.map (fun c => (c,2*c.owner+c.copy)) ∧
      operations (keyRowsQ cs)=10*cs.length+1 ∧
      allocations (keyRowsQ cs)=2*cs.length := by sorry
