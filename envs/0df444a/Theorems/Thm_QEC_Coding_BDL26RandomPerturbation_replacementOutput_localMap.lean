-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_replacementOutput_localMap
-- name    : QEC.Coding.BDL26RandomPerturbation.replacementOutput_localMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T23:23:42.867197+00:00
-- url     : https://prove2.me/theorems/9bae45a0-90db-4d96-9cc5-7c0839edb1f8
-- title:
--   BDL26 Random Perturbation: replacement Output local Map
-- statement:
--   Geometry and density of the actual resampled word determine the actual successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L113-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L113-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory
variable {L : ℝ}

theorem QEC.Coding.BDL26RandomPerturbation.replacementOutput_localMap (p : GeometricParameters L) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (hv : BoundedValence C.presentation)
    (hg : IncomingFaceGeometry C.presentation (perturbationOddScale p) J
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda))
    (hd : ∀ c, ((familyHits (oldTriangleImage C.presentation J)
      (Metric.closedBall c 1)).card : ℝ) ≤ triangleDensityBound) :
    IsBoundedDensityLocalMap (nextState (perturbationOddScale p) n C).presentation
      (replacementOutput (perturbationOddScale p) n C J) p.t := by sorry
