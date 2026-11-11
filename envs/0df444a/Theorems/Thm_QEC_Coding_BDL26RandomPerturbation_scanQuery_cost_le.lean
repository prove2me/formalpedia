-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_scanQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.scanQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:48:54.316639+00:00
-- url     : https://prove2.me/theorems/0dff557a-7e0b-45d3-bc3c-ccd4093faa98
-- title:
--   BDL26 Random Perturbation: scan Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the scan Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean#L32-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean#L32-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.scanQuery_cost_le {I Ω : Type*} (q : I → Ω → Bool × ℕ)
    (C : ℕ) (h : ∀ i ω, (q i ω).2 ≤ C) (L : List I) (ω : Ω) :
    (scanQuery q L ω).2 ≤ L.length*(C+1) := by sorry
