-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableLinear_actual
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.executableLinear_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:02:45.539066+00:00
-- url     : https://prove2.me/theorems/4da89a8a-afc2-4557-9a52-40d7dedc8f23
-- title:
--   BDL26 Global Lookup Linearity: executable Linear actual
-- statement:
--   Full agreement with the merged Tanner map through the ORIGINAL casts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L328-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L328-L332

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.executableLinear_actual (S : OddScale)
    (a : Word Bit (levelTwoPresentation S).Q) :
    executableLinear S (toExecutableError S a)=
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) a) := by sorry
