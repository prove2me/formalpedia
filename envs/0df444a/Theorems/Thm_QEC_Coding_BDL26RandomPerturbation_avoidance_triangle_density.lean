-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_avoidance_triangle_density
-- name    : QEC.Coding.BDL26RandomPerturbation.avoidance_triangle_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:16:37.707413+00:00
-- url     : https://prove2.me/theorems/0f67719b-218c-400b-b9c9-9248e8ca8880
-- title:
--   BDL26 Random Perturbation: avoidance triangle density
-- statement:
--   The BDL26 Random Perturbation construction uses the avoidance triangle density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AvoidanceDensity.lean#L10-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AvoidanceDensity.lean#L10-L60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NetCatch
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.avoidance_triangle_density (P : TannerSquarePresentation) (J w : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (hw : ∀ v, ‖w v‖ ≤ (6*p.m : ℕ)*(p.lambda : ℝ))
    (havoid : ∀ e : Event P J (anchorRadius p.m),
      w ∉ localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e)
    (z : Space) :
    ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
