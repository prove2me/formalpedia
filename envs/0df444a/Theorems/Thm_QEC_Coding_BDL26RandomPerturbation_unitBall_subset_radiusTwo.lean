-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_unitBall_subset_radiusTwo
-- name    : QEC.Coding.BDL26RandomPerturbation.unitBall_subset_radiusTwo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:57:28.992977+00:00
-- url     : https://prove2.me/theorems/25795e00-07eb-4ace-8c61-3cba0945d9fa
-- title:
--   BDL26 Random Perturbation: unit Ball subset radius Two
-- statement:
--   Nearest-grid enlargement sends every radius-one ball into a radius-two net ball.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean#L75-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean#L75-L81

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.unitBall_subset_radiusTwo (center net : Space) (h : dist center net ≤ 1) :
    Metric.closedBall center 1 ⊆ Metric.closedBall net 2 := by sorry
