-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_geometry_density
-- name    : QEC.Coding.BDL26KeyedGeometric.keyGood_geometry_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:47:13.809783+00:00
-- url     : https://prove2.me/theorems/54a922ea-4b54-4b22-9442-54c29be4e369
-- title:
--   BDL26 Keyed Geometric: key Good geometry density
-- statement:
--   Full deterministic geometry AND labeled density for every actual good assignment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L206-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L206-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.keyGood_geometry_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) (w : Vertex P → Space) (hw : w ∈ KeyGood P key hk J p) :
    IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
