-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_probability_real_le
-- name    : QEC.Coding.BDL26RandomPerturbation.event_probability_real_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:01:50.706722+00:00
-- url     : https://prove2.me/theorems/372e9f21-cd69-4be8-973b-8ac578f9a9d2
-- title:
--   BDL26 Random Perturbation: event probability real le
-- statement:
--   The BDL26 Random Perturbation construction uses the event probability real le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ProbabilityDecay.lean#L11-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ProbabilityDecay.lean#L11-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.event_probability_real_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P R c)).real
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ℝ)*(18*2/(R*(1-c)))^4 := by sorry
