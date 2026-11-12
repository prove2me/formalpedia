-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_empty
-- name    : QEC.Coding.BDL26NativeTriangleKeys.lookup_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:27:40.91314+00:00
-- url     : https://prove2.me/theorems/85761d7a-c2f8-468e-b554-ca75d9b4c149
-- title:
--   BDL26 Native Triangle Keys: lookup empty
-- statement:
--   The BDL26 Native Triangle Keys construction uses the lookup empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L103-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L103-L103

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.lookup_empty (c : Code) : lookupRowsQ c []=(none,1,0) := by sorry
