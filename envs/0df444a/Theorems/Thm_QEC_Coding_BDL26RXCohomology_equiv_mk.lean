-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_equiv_mk
-- name    : QEC.Coding.BDL26RXCohomology.equiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:14:11.733136+00:00
-- url     : https://prove2.me/theorems/2c8f351e-3daa-4247-bd3f-b5acc20b2389
-- title:
--   BDL26 RXCohomology: equiv mk
-- statement:
--   The BDL26 RXCohomology construction uses the equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L195-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L195-L199

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.equiv_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    equiv P A R S (classOf P v) =
      classOf (rxReplacementPresentation P S) (forwardCocycle P A R S v) := by sorry
