-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_actualGlobal_zero
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:47:07.033369+00:00
-- url     : https://prove2.me/theorems/a9b536b9-89ef-475b-aa48-93019193c075
-- title:
--   BDL26 Global Lookup Linearity: actual Global zero
-- statement:
--   The BDL26 Global Lookup Linearity construction uses the actual Global zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L367-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L367-L369

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_zero (S : OddScale) : actualGlobal S 0=0 := by sorry
