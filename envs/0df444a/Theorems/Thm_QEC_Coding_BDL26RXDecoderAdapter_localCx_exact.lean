-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_exact
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:10:00.173396+00:00
-- url     : https://prove2.me/theorems/223f844b-d851-4bfe-a4ae-241c243b6228
-- title:
--   BDL26 RXDecoder Adapter: local Cx exact
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cx exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/LocalComplexes.lean#L31-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/LocalComplexes.lean#L31-L44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_exact (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) :
    LinearMap.ker (wordLinearMapTranspose (localCx P S x).boundary2) =
      LinearMap.range (wordLinearMapTranspose (localCx P S x).boundary1) := by sorry
