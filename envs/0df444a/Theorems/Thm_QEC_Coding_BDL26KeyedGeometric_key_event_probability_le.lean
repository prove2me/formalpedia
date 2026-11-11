-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_probability_le
-- name    : QEC.Coding.BDL26KeyedGeometric.key_event_probability_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:58:35.967276+00:00
-- url     : https://prove2.me/theorems/7f975692-27b3-4bf9-a058-bce9e1859c43
-- title:
--   BDL26 Keyed Geometric: key event probability le
-- statement:
--   Joint triangle independence is derived before taking the finite union of grid centers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L89-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L89-L116

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

theorem QEC.Coding.BDL26KeyedGeometric.key_event_probability_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    Measure.pi (vertexLaw P R c)
      (localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ENNReal)*ENNReal.ofReal (18*2/(R*(1-c)))^4 := by sorry
