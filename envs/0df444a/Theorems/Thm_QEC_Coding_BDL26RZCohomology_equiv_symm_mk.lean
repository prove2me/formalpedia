-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_symm_mk
-- name    : QEC.Coding.BDL26RZCohomology.equiv_symm_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:38:24.84121+00:00
-- url     : https://prove2.me/theorems/e95a6bed-bfde-4bd6-a017-ff7b8d45a63f
-- title:
--   BDL26 RZCohomology: equiv symm mk
-- statement:
--   The BDL26 RZCohomology construction uses the equiv symm mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Equivalence.lean#L75-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Equivalence.lean#L75-L79

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance BDL26RZLocalReplacement

theorem QEC.Coding.BDL26RZCohomology.equiv_symm_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : Cocycle (successor P A4 S)) :
    (equiv P A4 R S).symm (classOf (successor P A4 S) w) =
      classOf P (backwardCocycle P A4 S w) := by sorry
