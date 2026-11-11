-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableLinear_apply
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.executableLinear_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:47:13.198136+00:00
-- url     : https://prove2.me/theorems/96c6bd0e-d89a-445c-819c-12582eaf7404
-- title:
--   BDL26 Global Lookup Linearity: executable Linear apply
-- statement:
--   The BDL26 Global Lookup Linearity construction uses the executable Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L324-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L324-L325

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.executableLinear_apply (S : OddScale) (a : Word Bit (ExecutableQ S)) :
    executableLinear S a=executableSyndrome S a := by sorry
