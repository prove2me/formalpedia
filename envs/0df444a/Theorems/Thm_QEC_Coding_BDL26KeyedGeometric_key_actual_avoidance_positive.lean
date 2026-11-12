-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_actual_avoidance_positive
-- name    : QEC.Coding.BDL26KeyedGeometric.key_actual_avoidance_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:46.010609+00:00
-- url     : https://prove2.me/theorems/1253390c-6929-4c63-b94b-b09dfd218a4a
-- title:
--   BDL26 Keyed Geometric: key actual avoidance positive
-- statement:
--   The actual continuous product law gives positive mass to simultaneous avoidance.
--   All dependency and probability hypotheses are derived from the incoming density and valence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L40-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L40-L59

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

theorem QEC.Coding.BDL26KeyedGeometric.key_actual_avoidance_positive (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (avoid (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ) := by sorry
