-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_rawKey_spec
-- name    : QEC.Coding.BDL26NativeTriangleKeys.rawKey_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:26:55.713727+00:00
-- url     : https://prove2.me/theorems/52ae3dba-4adf-44a8-a06d-233881bc8062
-- title:
--   BDL26 Native Triangle Keys: raw Key spec
-- statement:
--   The BDL26 Native Triangle Keys construction uses the raw Key spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L76-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L76-L78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.rawKey_spec (c : Code) :
    (rawKeyQ c).1=2*c.owner+c.copy ∧ operations (rawKeyQ c)=5 ∧
      allocations (rawKeyQ c)=0 := by sorry
