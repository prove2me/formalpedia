-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventScanKey_length
-- name    : QEC.Coding.BDL26RandomPerturbation.eventScanKey_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:51:54.249983+00:00
-- url     : https://prove2.me/theorems/52ecd578-807b-45ca-ac25-1d577ebb2312
-- title:
--   BDL26 Random Perturbation: event Scan Key length
-- statement:
--   The BDL26 Random Perturbation construction uses the event Scan Key length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventEncoding.lean#L26-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventEncoding.lean#L26-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Mathlib.Data.List.Lex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventScanKey_length (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : (eventScanKey P J radius e).length = 4 := by sorry
