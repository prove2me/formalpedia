-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateEventQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.stateEventQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:02:01.334015+00:00
-- url     : https://prove2.me/theorems/b3622995-506d-4bc8-b0dc-aa5e4cdeea80
-- title:
--   BDL26 Random Perturbation: state Event Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the state Event Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L72-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L72-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.stateEventQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    (stateEventQuery P J r lambda K e R).1 = true ↔
      statePoints R ∈ localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r lambda K) e := by sorry
