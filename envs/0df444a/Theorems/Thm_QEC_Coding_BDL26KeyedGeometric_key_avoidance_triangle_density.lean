-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_avoidance_triangle_density
-- name    : QEC.Coding.BDL26KeyedGeometric.key_avoidance_triangle_density
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:59:16.179718+00:00
-- url     : https://prove2.me/theorems/c69b3da4-72cc-4576-a1cd-31805cf9e244
-- title:
--   BDL26 Keyed Geometric: key avoidance triangle density
-- statement:
--   The BDL26 Keyed Geometric construction uses the key avoidance triangle density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L91-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L91-L142

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

theorem QEC.Coding.BDL26KeyedGeometric.key_avoidance_triangle_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J w : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (hw : ∀ v, ‖w v‖ ≤ (6*p.m : ℕ)*(p.lambda : ℝ))
    (havoid : ∀ e : KeyEvent P key hk J (anchorRadius p.m),
      w ∉ localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e)
    (z : Space) :
    ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
