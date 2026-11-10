-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_mk
-- name    : QEC.Coding.BDL26RZCohomology.equiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:39:24.135252+00:00
-- url     : https://prove2.me/theorems/1d41d595-9a64-49db-9cba-ebd3f46cba4a
-- title:
--   BDL26 RZCohomology: equiv mk
-- statement:
--   The BDL26 RZCohomology construction uses the equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Equivalence.lean#L69-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Equivalence.lean#L69-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance BDL26RZLocalReplacement

theorem QEC.Coding.BDL26RZCohomology.equiv_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    equiv P A4 R S (classOf P v) =
      classOf (successor P A4 S) (forwardCocycle P A4 S v) := by sorry
