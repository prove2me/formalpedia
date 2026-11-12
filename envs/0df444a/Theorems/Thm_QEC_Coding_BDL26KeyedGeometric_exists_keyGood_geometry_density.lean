-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_exists_keyGood_geometry_density
-- name    : QEC.Coding.BDL26KeyedGeometric.exists_keyGood_geometry_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:02:33.834028+00:00
-- url     : https://prove2.me/theorems/7856b251-0ce5-4b81-b4ef-d816312765f3
-- title:
--   BDL26 Keyed Geometric: exists key Good geometry density
-- statement:
--   Existence follows from the positive ORIGINAL product measure, never from a supplied witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L221-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L221-L236

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

theorem QEC.Coding.BDL26KeyedGeometric.exists_keyGood_geometry_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    ∃ w : Vertex P → Space, w ∈ KeyGood P key hk J p ∧
      IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
