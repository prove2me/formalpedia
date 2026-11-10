-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
-- name    : QEC.Coding.BDL26RZCohomology.forward_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:00:45.032974+00:00
-- url     : https://prove2.me/theorems/f84f008a-b9ce-43de-adae-57f51ac0184b
-- title:
--   BDL26 RZCohomology: forward mk
-- statement:
--   The BDL26 RZCohomology construction uses the forward mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Representatives.lean#L133-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Representatives.lean#L133-L136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance

theorem QEC.Coding.BDL26RZCohomology.forward_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (v : Cocycle P) :
    forward P A4 S (classOf P v) =
      classOf (successor P A4 S) (forwardCocycle P A4 S v) := by sorry

attribute [defeq] QEC.Coding.BDL26RZCohomology.forward_mk
