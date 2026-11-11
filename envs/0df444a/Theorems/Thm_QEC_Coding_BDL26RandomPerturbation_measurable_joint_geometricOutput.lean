-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_geometricOutput
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_joint_geometricOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:48:56.045805+00:00
-- url     : https://prove2.me/theorems/4a4e20dc-e768-4b7c-8957-04fb42dc06e5
-- title:
--   BDL26 Random Perturbation: measurable joint geometric Output
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable joint geometric Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L297-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L297-L316

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_joint_geometricOutput (P : TannerSquarePresentation)
    {L : ℝ} (p : GeometricParameters L) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        geometricOutput P z.1 p z.2) := by sorry
