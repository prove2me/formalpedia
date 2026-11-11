-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_actualGlobal_preimage
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:28:29.969415+00:00
-- url     : https://prove2.me/theorems/0bb3d75a-3956-4f16-8152-50e44416bd4c
-- title:
--   BDL26 Global Lookup Linearity: actual Global preimage
-- statement:
--   Full same-map preimage on actual ORIGINAL Tanner syndromes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L388-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L388-L405

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_preimage (S : OddScale) (a : Word Bit (levelTwoPresentation S).Q) :
    tannerCoboundary1 (levelTwoPresentation S)
      (actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a))=
      tannerCoboundary1 (levelTwoPresentation S) a := by sorry
