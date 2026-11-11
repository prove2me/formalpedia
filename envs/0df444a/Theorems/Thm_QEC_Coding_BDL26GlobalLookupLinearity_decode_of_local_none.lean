-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_decode_of_local_none
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.decode_of_local_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:07:49.592927+00:00
-- url     : https://prove2.me/theorems/6bb86b40-461c-4156-b7d9-b43ec52b7ad9
-- title:
--   BDL26 Global Lookup Linearity: decode of local none
-- statement:
--   Full old physical selector equality on its actual failed-local-search branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L415-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L415-L420

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.decode_of_local_none (S : OddScale) (s : Word Bit (levelTwoPresentation S).Z)
    (h : search (fun e => executableLocal S e &&
      decide (executableSyndrome S e=toExecutableSyndrome S s))
      (allWords (ExecutableQ S))=none) : decode S s=actualGlobal S s := by sorry
