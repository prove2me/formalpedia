-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_card_le
-- name    : QEC.Coding.BDL26RandomPerturbation.event_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:00:40.368853+00:00
-- url     : https://prove2.me/theorems/3268ece0-f833-4814-8d7f-a83c76bfc15e
-- title:
--   BDL26 Random Perturbation: event card le
-- statement:
--   The BDL26 Random Perturbation construction uses the event card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L71-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L71-L83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.event_card_le (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ) :
    Fintype.card (Event P J radius) ≤ Fintype.card (Triangle P)^4 := by sorry
