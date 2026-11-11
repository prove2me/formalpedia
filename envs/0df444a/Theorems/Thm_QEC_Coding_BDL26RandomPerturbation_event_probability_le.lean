-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_probability_le
-- name    : QEC.Coding.BDL26RandomPerturbation.event_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:01:31.583582+00:00
-- url     : https://prove2.me/theorems/d958ca24-6d8d-472b-a33d-8a22ab9d5d66
-- title:
--   BDL26 Random Perturbation: event probability le
-- statement:
--   Joint triangle independence is derived before taking the finite union of grid centers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventProbability.lean#L12-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventProbability.lean#L12-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.event_probability_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    Measure.pi (vertexLaw P R c)
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ENNReal)*ENNReal.ofReal (18*2/(R*(1-c)))^4 := by sorry
