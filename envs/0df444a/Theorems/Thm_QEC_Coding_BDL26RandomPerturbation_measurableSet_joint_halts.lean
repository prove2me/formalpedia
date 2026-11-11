-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_joint_halts
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_joint_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:44:16.675677+00:00
-- url     : https://prove2.me/theorems/90577bb2-e232-45a2-8505-c4feecb9369d
-- title:
--   BDL26 Random Perturbation: measurable Set joint halts
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set joint halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L279-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L279-L286

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

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_joint_halts (P : TannerSquarePresentation) (r lambda : ℝ)
    (K : ℕ) : MeasurableSet
      {z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) |
        Halts (eventSupport P z.1 r) (eventBad P z.1 r lambda K) z.2} := by sorry
