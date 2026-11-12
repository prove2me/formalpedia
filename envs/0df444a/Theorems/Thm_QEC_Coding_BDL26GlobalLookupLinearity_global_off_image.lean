-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_global_off_image
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.global_off_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:43:15.028113+00:00
-- url     : https://prove2.me/theorems/7873e2d0-cffc-4f7f-aa32-6a9edb2c22fd
-- title:
--   BDL26 Global Lookup Linearity: global off image
-- statement:
--   The default is retained outside the image, with no additivity claim there.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L183-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L183-L189

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.global_off_image (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∉LinearMap.range L) : G L s=0 := by sorry
