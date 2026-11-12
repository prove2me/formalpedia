-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableGlobal_residual
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:47:45.118457+00:00
-- url     : https://prove2.me/theorems/87ebb937-fc4c-4f70-9643-8dac8e5d9672
-- title:
--   BDL26 Global Lookup Linearity: executable Global residual
-- statement:
--   The BDL26 Global Lookup Linearity construction uses the executable Global residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L351-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L351-L353

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_residual (S : OddScale) (a : Word Bit (ExecutableQ S)) :
    executableSyndrome S (a+executableGlobal S (executableSyndrome S a))=0 := by sorry
