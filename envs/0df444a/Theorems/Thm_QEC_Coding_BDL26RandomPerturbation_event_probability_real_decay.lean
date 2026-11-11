-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_probability_real_decay
-- name    : QEC.Coding.BDL26RandomPerturbation.event_probability_real_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:03:17.602385+00:00
-- url     : https://prove2.me/theorems/3c1a4f16-9bb3-48db-9b00-3a9e0665c315
-- title:
--   BDL26 Random Perturbation: event probability real decay
-- statement:
--   The BDL26 Random Perturbation construction uses the event probability real decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ProbabilityDecay.lean#L31-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ProbabilityDecay.lean#L31-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.event_probability_real_decay (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (a lambda : ℕ) (ha : 0 < a) (hl : 1 ≤ lambda)
    (e : Event P J radius) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P ((a : ℝ)*lambda) c)).real
      (localEvent (eventSupport P J radius)
        (eventBad P J radius lambda ((a+2)*lambda)) e) ≤
      probabilityCoefficient a c/(lambda : ℝ) := by sorry
