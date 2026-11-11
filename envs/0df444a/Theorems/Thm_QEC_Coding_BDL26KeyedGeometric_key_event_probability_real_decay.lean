-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_probability_real_decay
-- name    : QEC.Coding.BDL26KeyedGeometric.key_event_probability_real_decay
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:02:03.169693+00:00
-- url     : https://prove2.me/theorems/aa563f5e-a20b-4856-b0f8-d884ad3cf749
-- title:
--   BDL26 Keyed Geometric: key event probability real decay
-- statement:
--   The BDL26 Keyed Geometric construction uses the key event probability real decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L139-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L139-L172

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

theorem QEC.Coding.BDL26KeyedGeometric.key_event_probability_real_decay (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (a lambda : ℕ) (ha : 0 < a) (hl : 1 ≤ lambda)
    (e : KeyEvent P key hk J radius) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P ((a : ℝ)*lambda) c)).real
      (localEvent (keySupport P key hk J radius)
        (keyBad P key hk J radius lambda ((a+2)*lambda)) e) ≤
      probabilityCoefficient a c/(lambda : ℝ) := by sorry
