-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_constant_doubleCylinder_coboundary
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.constant_doubleCylinder_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:38:20.234433+00:00
-- url     : https://prove2.me/theorems/8b8203e3-6d20-4231-b8c8-2842dcd67ec2
-- title:
--   BDL26 Replacement Cochain Maps: constant double Cylinder coboundary
-- statement:
--   The BDL26 Replacement Cochain Maps construction uses the constant double Cylinder coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L352-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L352-L363

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.constant_doubleCylinder_coboundary
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
        (fun _ => (1 : Field)) = 0 := by sorry
