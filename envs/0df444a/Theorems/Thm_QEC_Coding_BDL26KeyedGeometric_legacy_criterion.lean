-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_criterion
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:59:48.039395+00:00
-- url     : https://prove2.me/theorems/8d7087b0-b646-4347-b041-6a1ba65a01f8
-- title:
--   BDL26 Keyed Geometric: legacy criterion
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L149-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L149-L157

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26KeyedGeometric.legacy_criterion (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) (e : Event P J (anchorRadius p.m)) :
    (geometricLaw P p).real (localEvent (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M) *
        ∏ _f ∈ (supportGraph (eventSupport P J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) := by sorry
