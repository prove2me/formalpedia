-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_probability
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:00:19.764409+00:00
-- url     : https://prove2.me/theorems/f29625d7-b079-4e30-b345-4f5bd7cf0469
-- title:
--   BDL26 Keyed Geometric: legacy probability
-- statement:
--   The new probability proof recovers the original WHOLE legacy event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L142-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L142-L147

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26KeyedGeometric.legacy_probability (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (e : Event P J (anchorRadius p.m)) :
    (geometricLaw P p).real (localEvent (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) := by sorry
