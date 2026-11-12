-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_imageSection_preimage
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.imageSection_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:45:55.84048+00:00
-- url     : https://prove2.me/theorems/a9da685c-3b63-42ee-a83e-9b66c1c1a1d5
-- title:
--   BDL26 Global Lookup Linearity: image Section preimage
-- statement:
--   The BDL26 Global Lookup Linearity construction uses the image Section preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L268-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L268-L270

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.imageSection_preimage (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : LinearMap.range L) : L (imageSection L s)=s.val := by sorry
