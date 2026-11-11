-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventKeyQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventKeyQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:54:35.532371+00:00
-- url     : https://prove2.me/theorems/64ebc529-1ccd-40fb-a54a-b4451be212b3
-- title:
--   BDL26 Random Perturbation: event Key Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the event Key Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L130-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L130-L147

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventKeyQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) :
    (eventKeyQuery P J radius e).2 ≤ 4*(Fintype.card (Triangle P)+1)+50 := by sorry
