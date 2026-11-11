-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableGlobal_add
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:26:56.306561+00:00
-- url     : https://prove2.me/theorems/ed83b289-c761-4da6-90c5-dd2241ac124e
-- title:
--   BDL26 Global Lookup Linearity: executable Global add
-- statement:
--   All OddScale, all original physical words; no small-support hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L346-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L346-L349

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_add (S : OddScale) (a b : Word Bit (ExecutableQ S)) :
    executableGlobal S (executableSyndrome S a+executableSyndrome S b)=
      executableGlobal S (executableSyndrome S a)+executableGlobal S (executableSyndrome S b) := by sorry
