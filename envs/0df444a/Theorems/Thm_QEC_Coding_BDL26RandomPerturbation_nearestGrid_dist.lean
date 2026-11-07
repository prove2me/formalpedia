-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_nearestGrid_dist
-- name    : QEC.Coding.BDL26RandomPerturbation.nearestGrid_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:36:08.965101+00:00
-- url     : https://prove2.me/theorems/bef78c3a-b622-4968-b3d3-76526b1fbcff
-- title:
--   BDL26 Random Perturbation: nearest Grid dist
-- statement:
--   The BDL26 Random Perturbation construction uses the nearest Grid dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean#L40-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean#L40-L57

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.nearestGrid_dist (K : ℕ) (p : Space) (hp : ‖p‖ ≤ K) :
    dist p (gridPoint K (nearestGrid K p hp)) ≤ 1 := by sorry
