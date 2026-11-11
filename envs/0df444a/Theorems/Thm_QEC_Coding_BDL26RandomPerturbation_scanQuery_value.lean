-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_scanQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.scanQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:43:49.176199+00:00
-- url     : https://prove2.me/theorems/e0b8c699-d490-4521-9bfa-b5c92330af16
-- title:
--   BDL26 Random Perturbation: scan Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the scan Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean#L19-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean#L19-L30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.scanQuery_value {I Ω : Type*} (q : I → Ω → Bool × ℕ)
    (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
    (h : ∀ i ω, (q i ω).1 = true ↔ ω ∈ B i) (L : List I) (ω : Ω) :
    (scanQuery q L ω).1 = firstBadFrom B L ω := by sorry
