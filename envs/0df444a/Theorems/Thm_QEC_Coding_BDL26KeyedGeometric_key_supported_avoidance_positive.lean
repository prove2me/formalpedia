-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_supported_avoidance_positive
-- name    : QEC.Coding.BDL26KeyedGeometric.key_supported_avoidance_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:01:54.761306+00:00
-- url     : https://prove2.me/theorems/8ecf49e0-2c78-4998-bc25-024c3c2f5c0e
-- title:
--   BDL26 Keyed Geometric: key supported avoidance positive
-- statement:
--   Intersecting with the cap-supported assignments preserves all positive avoidance mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L157-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L157-L165

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

theorem QEC.Coding.BDL26KeyedGeometric.key_supported_avoidance_positive (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ KeyAvoid P key hk J p) := by sorry
