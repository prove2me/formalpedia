-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_masterBad_original
-- name    : QEC.Coding.BDL26RandomPerturbation.masterBad_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:01:23.262299+00:00
-- url     : https://prove2.me/theorems/94fd3a23-726e-4563-85bc-d491a1a5e548
-- title:
--   BDL26 Random Perturbation: master Bad original
-- statement:
--   The BDL26 Random Perturbation construction uses the master Bad original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L169-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L169-L178

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

theorem QEC.Coding.BDL26RandomPerturbation.masterBad_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r)
    (u : eventSupport P J r e → Space) :
    u ∈ masterBad P r lambda K J (eventToMaster P J r e) ↔
      u ∈ eventBad P J r lambda K e := by sorry
