-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_probability_real_bound
-- name    : QEC.Coding.BDL26KeyedGeometric.key_probability_real_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:43:57.230317+00:00
-- url     : https://prove2.me/theorems/b8dd6586-7357-43c6-9291-a4763bfa3ea7
-- title:
--   BDL26 Keyed Geometric: key probability real bound
-- statement:
--   The complete numerical parameters give the actual keyed event's required bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L218-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L218-L227

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26KeyedGeometric.key_probability_real_bound (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (e : KeyEvent P key hk J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) := by sorry
