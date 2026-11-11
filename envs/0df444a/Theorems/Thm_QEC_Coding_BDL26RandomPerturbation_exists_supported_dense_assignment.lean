-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_supported_dense_assignment
-- name    : QEC.Coding.BDL26RandomPerturbation.exists_supported_dense_assignment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T22:27:05.096193+00:00
-- url     : https://prove2.me/theorems/6ceb5649-cd74-4132-b8df-3b366ea7338a
-- title:
--   BDL26 Random Perturbation: exists supported dense assignment
-- statement:
--   An actual finite-product sample has all cap constraints, avoids every geometric event,
--   and obeys the desired density of labeled auxiliary triangles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L59-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L59-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.exists_supported_dense_assignment (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    ∃ w : Vertex P → Space, w ∈ geometricSupport P p ∧ w ∈ geometricAvoidance P J p ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
