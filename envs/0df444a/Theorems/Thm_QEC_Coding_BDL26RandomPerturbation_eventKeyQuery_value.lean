-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventKeyQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.eventKeyQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:10:37.985786+00:00
-- url     : https://prove2.me/theorems/e2e8b60a-8399-407a-ae3d-bd2f36ee1094
-- title:
--   BDL26 Random Perturbation: event Key Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the event Key Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L107-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L107-L128

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventKeyQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) :
    (eventKeyQuery P J radius e).1 = eventScanKey P J radius e := by sorry
