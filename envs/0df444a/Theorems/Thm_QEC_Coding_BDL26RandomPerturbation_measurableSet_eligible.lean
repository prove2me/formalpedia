-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eligible
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_eligible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:00:30.33723+00:00
-- url     : https://prove2.me/theorems/1ccd8f1e-ba49-4f56-b9e1-5fda29df5e65
-- title:
--   BDL26 Random Perturbation: measurable Set eligible
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set eligible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L107-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L107-L135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_eligible (P : TannerSquarePresentation) (s : Finset (Triangle P))
    (r : ℝ) : MeasurableSet {J : Vertex P → Space | Eligible P J r s} := by sorry
