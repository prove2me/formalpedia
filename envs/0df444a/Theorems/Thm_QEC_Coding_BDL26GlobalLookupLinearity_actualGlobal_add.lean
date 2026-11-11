-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_actualGlobal_add
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:48:03.344986+00:00
-- url     : https://prove2.me/theorems/fbc35747-51c3-41f6-b626-a00a27582dd1
-- title:
--   BDL26 Global Lookup Linearity: actual Global add
-- statement:
--   Complete addition identity for actual ORIGINAL Tanner words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L372-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L372-L385

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_add (S : OddScale) (a b : Word Bit (levelTwoPresentation S).Q) :
    actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a+
      tannerCoboundary1 (levelTwoPresentation S) b)=
      actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a)+
      actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) b) := by sorry
