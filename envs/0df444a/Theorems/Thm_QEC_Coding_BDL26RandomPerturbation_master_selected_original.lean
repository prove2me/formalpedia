-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_selected_original
-- name    : QEC.Coding.BDL26RandomPerturbation.master_selected_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:45:05.211979+00:00
-- url     : https://prove2.me/theorems/1ac0e864-525b-4ccb-843b-1da33742f33b
-- title:
--   BDL26 Random Perturbation: master selected original
-- statement:
--   The BDL26 Random Perturbation construction uses the master selected original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L223-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L223-L231

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

theorem QEC.Coding.BDL26RandomPerturbation.master_selected_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    (selected (eventSupport P J r) (eventBad P J r lambda K) T n).map
        (eventToMaster P J r) =
      selected (masterSupport P) (masterBad P r lambda K J) T n := by sorry
