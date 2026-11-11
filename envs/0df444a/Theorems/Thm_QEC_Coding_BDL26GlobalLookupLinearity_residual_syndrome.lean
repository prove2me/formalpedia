-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_residual_syndrome
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.residual_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:26:45.226113+00:00
-- url     : https://prove2.me/theorems/4a274af8-3e9f-4ee3-acd6-1f959c3279b4
-- title:
--   BDL26 Global Lookup Linearity: residual syndrome
-- statement:
--   Residual of every original word lies in the true kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L273-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L273-L276

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.residual_syndrome (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a : Word Bit A) : L (a+G L (L a))=0 := by sorry
