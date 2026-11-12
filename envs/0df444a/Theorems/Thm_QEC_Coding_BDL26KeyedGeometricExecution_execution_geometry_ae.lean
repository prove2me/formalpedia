-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_execution_geometry_ae
-- name    : QEC.Coding.BDL26KeyedGeometricExecution.execution_geometry_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:49:24.642923+00:00
-- url     : https://prove2.me/theorems/622d68f4-ef34-4efe-b004-38121327d514
-- title:
--   BDL26 Keyed Geometric Execution: execution geometry ae
-- statement:
--   Whole generic execution endpoint: actual table law, halting, cap support,
--   complete face geometry, and every-center labeled density for this output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L201-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L201-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometricExecution
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26KeyedGeometricExecution.execution_geometry_ae (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    Measurable (result P k hk J p) ∧
    ∀ᵐ T ∂tableMeasure P p,
      Halts (keySupport P k hk J (anchorRadius p.m))
        (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      result P k hk J p T ∈ KeyGood P k hk J p ∧
      IncomingFaceGeometry P (perturbationOddScale p)
        (perturbedMap P J p.lambda (result P k hk J p T))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (result P k hk J p T)))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
