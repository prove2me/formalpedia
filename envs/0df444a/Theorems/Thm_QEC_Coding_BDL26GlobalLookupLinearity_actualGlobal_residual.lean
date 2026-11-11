-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_actualGlobal_residual
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:28:55.06663+00:00
-- url     : https://prove2.me/theorems/0564ee48-5fdc-44e9-bddd-76e8f31aa0e1
-- title:
--   BDL26 Global Lookup Linearity: actual Global residual
-- statement:
--   Full original residual has zero syndrome; no boundary/filling claim follows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L408-L412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L408-L412

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_residual (S : OddScale) (a : Word Bit (levelTwoPresentation S).Q) :
    tannerCoboundary1 (levelTwoPresentation S)
      (a+actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a))=0 := by sorry
