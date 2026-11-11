-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_avoidance_geometry_density
-- name    : QEC.Coding.BDL26RandomPerturbation.supported_avoidance_geometry_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:31:21.834576+00:00
-- url     : https://prove2.me/theorems/37ad20c1-6cd1-412a-85ff-3a0c426ee820
-- title:
--   BDL26 Random Perturbation: supported avoidance geometry density
-- statement:
--   The measured positive-probability event has actual geometry and labeled density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L27-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L27-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.supported_avoidance_geometry_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (w : Vertex P → Space) (hw : w ∈ geometricSupport P p ∩ geometricAvoidance P J p) :
    IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
