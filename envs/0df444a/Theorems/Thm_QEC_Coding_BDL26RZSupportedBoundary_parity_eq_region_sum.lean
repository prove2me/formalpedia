-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZSupportedBoundary_parity_eq_region_sum
-- name    : QEC.Coding.BDL26RZSupportedBoundary.parity_eq_region_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:19:06.408197+00:00
-- url     : https://prove2.me/theorems/e1079d9c-b226-4656-9c65-c5498a707378
-- title:
--   BDL26 RZSupported Boundary: parity eq region sum
-- statement:
--   The BDL26 RZSupported Boundary construction uses the parity eq region sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZSupportedBoundary.lean#L151-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZSupportedBoundary.lean#L151-L154

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

theorem QEC.Coding.BDL26RZSupportedBoundary.parity_eq_region_sum (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (r : topSpace P S z) :
    parity P S z r = ∑ p ∈ blockRegion P S z, r.1 p := by sorry
