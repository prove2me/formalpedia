-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_geometricSupport
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_geometricSupport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:07:18.669578+00:00
-- url     : https://prove2.me/theorems/17cb5bce-0fd2-4b95-ab1c-245d3a3b6afb
-- title:
--   BDL26 Random Perturbation: measurable Set geometric Support
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set geometric Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L25-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L25-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_geometricSupport (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : MeasurableSet (geometricSupport P p) := by sorry
