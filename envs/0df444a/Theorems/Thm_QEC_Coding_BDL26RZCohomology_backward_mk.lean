-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
-- name    : QEC.Coding.BDL26RZCohomology.backward_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:01:00.960265+00:00
-- url     : https://prove2.me/theorems/cd1c557e-3688-4933-8f26-379c137d14bf
-- title:
--   BDL26 RZCohomology: backward mk
-- statement:
--   The BDL26 RZCohomology construction uses the backward mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Representatives.lean#L138-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Representatives.lean#L138-L141

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance

theorem QEC.Coding.BDL26RZCohomology.backward_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (w : Cocycle (successor P A4 S)) :
    backward P A4 S (classOf (successor P A4 S) w) =
      classOf P (backwardCocycle P A4 S w) := by sorry

attribute [defeq] QEC.Coding.BDL26RZCohomology.backward_mk
