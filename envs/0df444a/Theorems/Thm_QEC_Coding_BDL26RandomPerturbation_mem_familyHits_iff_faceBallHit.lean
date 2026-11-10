-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mem_familyHits_iff_faceBallHit
-- name    : QEC.Coding.BDL26RandomPerturbation.mem_familyHits_iff_faceBallHit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:07:41.966439+00:00
-- url     : https://prove2.me/theorems/7be9587c-e352-44ed-a8c0-35fe8f1b237b
-- title:
--   BDL26 Random Perturbation: mem family Hits iff face Ball Hit
-- statement:
--   The BDL26 Random Perturbation construction uses the mem family Hits iff face Ball Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L21-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L21-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

theorem QEC.Coding.BDL26RandomPerturbation.mem_familyHits_iff_faceBallHit (P : TannerSquarePresentation)
    (J : Vertex P → Space) (f : P.Face) (c : Space) :
    f ∈ familyHits (tannerFaceImage P J) (Metric.closedBall c 1) ↔
      faceBallHit P J f c := by sorry
