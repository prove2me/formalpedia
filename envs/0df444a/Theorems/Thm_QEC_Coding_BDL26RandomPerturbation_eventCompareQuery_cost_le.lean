-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventCompareQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:11:36.10561+00:00
-- url     : https://prove2.me/theorems/ea696d0c-6959-4b5b-9c93-6f845de492e5
-- title:
--   BDL26 Random Perturbation: event Compare Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the event Compare Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L162-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L162-L172

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) :
    (eventCompareQuery P J radius e f).2 ≤ 8*(Fintype.card (Triangle P)+1)+109 := by sorry
