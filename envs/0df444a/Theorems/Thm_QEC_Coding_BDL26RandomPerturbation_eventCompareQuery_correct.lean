-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventCompareQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:11:20.748004+00:00
-- url     : https://prove2.me/theorems/6ae4bef2-1e1e-4859-9ffd-0d0a6b252806
-- title:
--   BDL26 Random Perturbation: event Compare Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the event Compare Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L156-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L156-L160

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) :
    (eventCompareQuery P J radius e f).1 = true ↔
      eventScanKey P J radius e ≤ eventScanKey P J radius f := by sorry
