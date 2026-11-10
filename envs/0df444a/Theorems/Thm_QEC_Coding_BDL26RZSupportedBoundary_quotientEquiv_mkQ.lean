-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZSupportedBoundary_quotientEquiv_mkQ
-- name    : QEC.Coding.BDL26RZSupportedBoundary.quotientEquiv_mkQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:18:29.107367+00:00
-- url     : https://prove2.me/theorems/9dd3a97c-8ae8-4808-98a1-88ffe6b5a2a3
-- title:
--   BDL26 RZSupported Boundary: quotient Equiv mk Q
-- statement:
--   The BDL26 RZSupported Boundary construction uses the quotient Equiv mk Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZSupportedBoundary.lean#L213-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZSupportedBoundary.lean#L213-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZSupportedBoundary
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26RZConcreteParity
open MultiscaleDecoder
open MultiscaleDecoder.RZCoarseGraining.RZCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RZSupportedBoundary.quotientEquiv_mkQ (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (r : topSpace P S z) :
    quotientEquiv P A S z ((LinearMap.range (boundary P A S z)).mkQ r) =
      ∑ p ∈ blockRegion P S z, r.1 p := by sorry
