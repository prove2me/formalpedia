-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_scaled_grid_card_le
-- name    : QEC.Coding.BDL26RandomPerturbation.scaled_grid_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:03:08.0502+00:00
-- url     : https://prove2.me/theorems/ba43cac1-3fb5-4d9b-926c-a576c7fe6996
-- title:
--   BDL26 Random Perturbation: scaled grid card le
-- statement:
--   At integral scale lambda>=1 the grid count is cubic with a scale-independent coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventProbability.lean#L41-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventProbability.lean#L41-L47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.scaled_grid_card_le (a lambda : ℕ) (hl : 1 ≤ lambda) :
    Fintype.card (Grid (a*lambda)) ≤ (2*a+1)^3*lambda^3 := by sorry
