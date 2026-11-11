-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_halts_original
-- name    : QEC.Coding.BDL26RandomPerturbation.master_halts_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:46:58.07099+00:00
-- url     : https://prove2.me/theorems/4a9bf918-67fb-443c-8506-7e477c68843f
-- title:
--   BDL26 Random Perturbation: master halts original
-- statement:
--   The BDL26 Random Perturbation construction uses the master halts original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L233-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L233-L237

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

theorem QEC.Coding.BDL26RandomPerturbation.master_halts_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) :
    Halts (masterSupport P) (masterBad P r lambda K J) T ↔
      Halts (eventSupport P J r) (eventBad P J r lambda K) T := by sorry
