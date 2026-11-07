-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridCoordinate_card
-- name    : QEC.Coding.BDL26RandomPerturbation.gridCoordinate_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:35:23.200198+00:00
-- url     : https://prove2.me/theorems/a5c8abd3-2755-4dcd-985e-901b1cd553e3
-- title:
--   BDL26 Random Perturbation: grid Coordinate card
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Coordinate card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean#L16-L18
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean#L16-L18

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.gridCoordinate_card (K : ℕ) : Fintype.card (GridCoordinate K) = 2*K+1 := by sorry
