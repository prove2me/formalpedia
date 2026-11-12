-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_exists_supported_dense_assignment
-- name    : QEC.Coding.BDL26KeyedGeometric.key_exists_supported_dense_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:48:08.476569+00:00
-- url     : https://prove2.me/theorems/238ef7a8-71cb-4aac-b955-f65768dd6d1d
-- title:
--   BDL26 Keyed Geometric: key exists supported dense assignment
-- statement:
--   An actual finite-product sample has all cap constraints, avoids every geometric event,
--   and obeys the desired density of labeled auxiliary triangles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L169-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L169-L185

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

theorem QEC.Coding.BDL26KeyedGeometric.key_exists_supported_dense_assignment (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    ∃ w : Vertex P → Space, w ∈ geometricSupport P p ∧ w ∈ KeyAvoid P key hk J p ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
