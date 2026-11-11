-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_density_violation
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_density_violation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:07:43.15969+00:00
-- url     : https://prove2.me/theorems/668f7ef4-8a69-4083-8544-8549ea92efa0
-- title:
--   BDL26 Random Perturbation: measurable Set density violation
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable Set density violation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L139-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L139-L150

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_density_violation (P : TannerSquarePresentation) (t : ℝ) :
    MeasurableSet {J : Vertex P → Space |
      ∃ c, t < ((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ)} := by sorry
