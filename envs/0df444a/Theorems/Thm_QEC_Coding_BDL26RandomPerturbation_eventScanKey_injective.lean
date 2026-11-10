-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventScanKey_injective
-- name    : QEC.Coding.BDL26RandomPerturbation.eventScanKey_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:02:18.725076+00:00
-- url     : https://prove2.me/theorems/e6a3cffc-8bb6-4b5a-9096-44d18e7926d0
-- title:
--   BDL26 Random Perturbation: event Scan Key injective
-- statement:
--   The BDL26 Random Perturbation construction uses the event Scan Key injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventEncoding.lean#L18-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventEncoding.lean#L18-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Mathlib.Data.List.Lex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventScanKey_injective (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) : Function.Injective (eventScanKey P J radius) := by sorry
