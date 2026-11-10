-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventSupport_card_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventSupport_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:01:27.292058+00:00
-- url     : https://prove2.me/theorems/60b6df4e-c4bd-4fa0-b5de-2efb29be751f
-- title:
--   BDL26 Random Perturbation: event Support card le
-- statement:
--   The BDL26 Random Perturbation construction uses the event Support card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L56-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L56-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.eventSupport_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : (eventSupport P J radius e).card ≤ 12 := by sorry
