-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T22:11:19.623006+00:00
-- url     : https://prove2.me/theorems/b2c4f7e0-c5b3-4ea5-a27f-57e60cf4a792
-- title:
--   BDL26 Random Perturbation: event Query cost le
-- statement:
--   The fixed event uses four labeled triangles at each of its fixed grid centers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L74-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L74-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set

theorem QEC.Coding.BDL26RandomPerturbation.eventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    (p : eventSupport P J radius e → Space) :
    (eventQuery P J radius lambda K e p).2 ≤ Fintype.card (Grid K)*(4*200001+1) := by sorry
