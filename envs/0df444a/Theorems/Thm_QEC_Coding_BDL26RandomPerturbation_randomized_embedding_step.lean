-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_randomized_embedding_step
-- name    : QEC.Coding.BDL26RandomPerturbation.randomized_embedding_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:30:37.381951+00:00
-- url     : https://prove2.me/theorems/933836fd-7c5c-41a5-99e6-6135ea937e50
-- title:
--   BDL26 Random Perturbation: randomized embedding step
-- statement:
--   Joint size/depth-independent constants with finite-law and actual algorithm guarantees.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L85-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L85-L114

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.randomized_embedding_step (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower,
      (0 : ℝ) < triangleDensityBound ∧ (triangleDensityBound : ℝ) < p.t ∧
      ∀ (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (J : Vertex P → Space),
        IsBoundedDensityLocalMap P J p.t → BoundedValence P →
        letI (v : Vertex P) := vertexLaw_probability P
          ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
        0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) ∧
        Measurable (perturbationEmbeddingOutput P J p) ∧
        (∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
          Halts (eventSupport P J (anchorRadius p.m))
            (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
          IncomingFaceGeometry P (perturbationOddScale p)
            (perturbedMap P J p.lambda (geometricOutput P J p T))
            (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
          ∀ z, ((familyHits (oldTriangleImage P
            (perturbedMap P J p.lambda (geometricOutput P J p T)))
              (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound) ∧
        (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
          p.lambda ((6*p.m+2)*p.lambda) T
          ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
            (operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 : ℕ) := by sorry
