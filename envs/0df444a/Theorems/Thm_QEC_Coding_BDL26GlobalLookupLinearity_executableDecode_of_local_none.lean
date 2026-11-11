-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableDecode_of_local_none
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.executableDecode_of_local_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:27:46.815956+00:00
-- url     : https://prove2.me/theorems/918b5515-ffda-4788-b10b-0025bd853b52
-- title:
--   BDL26 Global Lookup Linearity: executable Decode of local none
-- statement:
--   No local-first linearity: this identity requires the LITERAL local-none branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L356-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L356-L360

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.executableDecode_of_local_none (S : OddScale) (s : Word Bit (ExecutableZ S))
    (h : search (fun e => executableLocal S e && decide (executableSyndrome S e=s))
      (allWords (ExecutableQ S))=none) :
    executableDecode S s=executableGlobal S s := by sorry
