-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_supported_geometry_density
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_supported_geometry_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:03:15.41388+00:00
-- url     : https://prove2.me/theorems/fb02af6f-f41f-414d-af83-04659d208b24
-- title:
--   BDL26 Keyed Geometric: legacy supported geometry density
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy supported geometry density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L159-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L159-L169

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26KeyedGeometric.legacy_supported_geometry_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) ∧
    ∀ w ∈ geometricSupport P p ∩ geometricAvoidance P J p,
      IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
