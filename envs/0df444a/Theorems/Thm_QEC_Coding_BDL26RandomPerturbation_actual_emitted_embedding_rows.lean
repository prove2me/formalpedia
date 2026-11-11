-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actual_emitted_embedding_rows
-- name    : QEC.Coding.BDL26RandomPerturbation.actual_emitted_embedding_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:16:15.020424+00:00
-- url     : https://prove2.me/theorems/9edec31f-0238-4d72-b362-93a7a881f110
-- title:
--   BDL26 Random Perturbation: actual emitted embedding rows
-- statement:
--   The counted output loop emits exactly the measurable geometric execution map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L72-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L72-L82

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

theorem QEC.Coding.BDL26RandomPerturbation.actual_emitted_embedding_rows (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    (outputStateRowsQuery P J p.lambda
      (actualPrefixQuery P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
        (eventUniverseQuery P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1 T
        (haltTime (eventSupport P J (anchorRadius p.m))
          (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)).1).1 =
      (vertexInputList P).map (fun v => (v,perturbationEmbeddingOutput P J p T v)) := by sorry
