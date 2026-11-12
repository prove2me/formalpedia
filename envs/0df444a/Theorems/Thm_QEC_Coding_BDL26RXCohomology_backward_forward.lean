-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_backward_forward
-- name    : QEC.Coding.BDL26RXCohomology.backward_forward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:44:25.624212+00:00
-- url     : https://prove2.me/theorems/ab185a95-b929-411e-9479-4decd3b1242d
-- title:
--   BDL26 RXCohomology: backward forward
-- statement:
--   The BDL26 RXCohomology construction uses the backward forward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L201-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L201-L204

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

theorem QEC.Coding.BDL26RXCohomology.backward_forward (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : H1 P) :
    (equiv P A R S).symm (equiv P A R S v) = v := by sorry
