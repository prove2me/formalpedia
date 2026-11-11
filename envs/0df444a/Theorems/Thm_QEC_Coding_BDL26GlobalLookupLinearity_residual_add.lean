-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_residual_add
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.residual_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:11:26.218105+00:00
-- url     : https://prove2.me/theorems/3625cb70-5f42-433f-9737-90aed5dd2acc
-- title:
--   BDL26 Global Lookup Linearity: residual add
-- statement:
--   Full residual addition equality, not just an equality of logical classes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L279-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L279-L283

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.residual_add (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a b : Word Bit A) :
    (a+b)+G L (L (a+b))=(a+G L (L a))+(b+G L (L b)) := by sorry
