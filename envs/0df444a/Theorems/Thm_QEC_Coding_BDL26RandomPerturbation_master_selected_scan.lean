-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_selected_scan
-- name    : QEC.Coding.BDL26RandomPerturbation.master_selected_scan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:46:58.416402+00:00
-- url     : https://prove2.me/theorems/2b2a084f-909b-4959-9531-7d860ad69dc0
-- title:
--   BDL26 Random Perturbation: master selected scan
-- statement:
--   The BDL26 Random Perturbation construction uses the master selected scan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L180-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L180-L191

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

theorem QEC.Coding.BDL26RandomPerturbation.master_selected_scan (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : Vertex P → Space) :
    (select (localEvent (eventSupport P J r) (eventBad P J r lambda K)) u).map
        (eventToMaster P J r) =
      select (localEvent (masterSupport P) (masterBad P r lambda K J)) u := by sorry
