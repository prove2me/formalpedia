-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_continuous_oldAnchor
-- name    : QEC.Coding.BDL26RandomPerturbation.continuous_oldAnchor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:45:44.716207+00:00
-- url     : https://prove2.me/theorems/66955d15-6ce6-4dd8-960c-445d8d711a15
-- title:
--   BDL26 Random Perturbation: continuous old Anchor
-- statement:
--   The BDL26 Random Perturbation construction uses the continuous old Anchor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L102-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/JointExecution.lean#L102-L105

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

theorem QEC.Coding.BDL26RandomPerturbation.continuous_oldAnchor (P : TannerSquarePresentation) (a : Triangle P) :
    Continuous (fun J : Vertex P → Space => oldAnchor P J a) := by sorry
