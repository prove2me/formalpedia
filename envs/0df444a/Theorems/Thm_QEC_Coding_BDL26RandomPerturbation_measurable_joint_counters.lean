-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_counters
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_joint_counters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:45:09.846546+00:00
-- url     : https://prove2.me/theorems/3e667990-87b3-4222-8ff1-787d155d2461
-- title:
--   BDL26 Random Perturbation: measurable joint counters
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable joint counters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L260-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L260-L267

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_joint_counters (P : TannerSquarePresentation) (r lambda : ℝ)
    (K n : ℕ) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        counters (eventSupport P z.1 r) (eventBad P z.1 r lambda K) z.2 n) := by sorry
