-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_density_violation_iff
-- name    : QEC.Coding.BDL26RandomPerturbation.density_violation_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:07:22.367205+00:00
-- url     : https://prove2.me/theorems/7cb8d008-7ee8-42cf-86d9-772760670ccc
-- title:
--   BDL26 Random Perturbation: density violation iff
-- statement:
--   The witness uses face DOMAIN labels and every real centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L120-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L120-L137

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

theorem QEC.Coding.BDL26RandomPerturbation.density_violation_iff (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) :
    (∃ c, t < ((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ)) ↔
      ∃ (N : ℕ) (s : Finset P.Face), t < (s.card : ℝ) ∧ J ∈ boundedLabelHit P s N := by sorry
