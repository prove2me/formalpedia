-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableGlobal_zero
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:26:15.564931+00:00
-- url     : https://prove2.me/theorems/1100a35e-2da9-48c6-93bf-e17ea7f988d3
-- title:
--   BDL26 Global Lookup Linearity: executable Global zero
-- statement:
--   The BDL26 Global Lookup Linearity construction uses the executable Global zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L338-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L338-L339

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_zero (S : OddScale) : executableGlobal S 0=0 := by sorry
