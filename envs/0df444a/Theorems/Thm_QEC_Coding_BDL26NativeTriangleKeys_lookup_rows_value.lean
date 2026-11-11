-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_rows_value
-- name    : QEC.Coding.BDL26NativeTriangleKeys.lookup_rows_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:17:13.181868+00:00
-- url     : https://prove2.me/theorems/e77999fe-315f-4358-9166-a876700f6ff6
-- title:
--   BDL26 Native Triangle Keys: lookup rows value
-- statement:
--   The BDL26 Native Triangle Keys construction uses the lookup rows value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L121-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L121-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleKeys.lookup_rows_value (c : Code) (cs : List Code) :
    (lookupRowsQ c (keyRowsQ cs).1).1=
      if c∈cs then some (2*c.owner+c.copy) else none := by sorry
