-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateEventQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.stateEventQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:03:50.534209+00:00
-- url     : https://prove2.me/theorems/3464cfbf-383b-4413-bfdc-697939524211
-- title:
--   BDL26 Random Perturbation: state Event Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the state Event Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L86-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L86-L107

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.stateEventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    (stateEventQuery P J r lambda K e R).2 ≤ stateQueryBudget (Fintype.card (Triangle P)) R.length K := by sorry
