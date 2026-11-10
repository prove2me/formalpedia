-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_forward_backward
-- name    : QEC.Coding.BDL26RXCohomology.forward_backward
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:44:21.031578+00:00
-- url     : https://prove2.me/theorems/d9cb6cd5-1416-4d89-a3ed-3c3ae56c077d
-- title:
--   BDL26 RXCohomology: forward backward
-- statement:
--   The BDL26 RXCohomology construction uses the forward backward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L206-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L206-L209

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.forward_backward (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : H1 (rxReplacementPresentation P S)) :
    equiv P A R S ((equiv P A R S).symm w) = w := by sorry
