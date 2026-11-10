-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_constant_qDoubleCylinder_coboundary
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.constant_qDoubleCylinder_coboundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:04:46.067724+00:00
-- url     : https://prove2.me/theorems/b1d0fb9f-3fc9-4128-a680-d7f58d57900b
-- title:
--   BDL26 Replacement Cochain Maps: constant q Double Cylinder coboundary
-- statement:
--   The BDL26 Replacement Cochain Maps construction uses the constant q Double Cylinder coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L396-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L396-L404

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.constant_qDoubleCylinder_coboundary
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun _ => (1 : Field)) = 0 := by sorry
