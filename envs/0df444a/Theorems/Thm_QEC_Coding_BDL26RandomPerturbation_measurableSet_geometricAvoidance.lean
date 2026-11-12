-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_geometricAvoidance
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_geometricAvoidance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:24:34.947997+00:00
-- url     : https://prove2.me/theorems/ba3c76fd-18af-4dd3-92ca-eb64b3dfc66c
-- title:
--   BDL26 Random Perturbation: measurable Set geometric Avoidance
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set geometric Avoidance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L31-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L31-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_geometricAvoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : MeasurableSet (geometricAvoidance P J p) := by sorry
