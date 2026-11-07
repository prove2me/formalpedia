-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridPointQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.gridPointQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:57:52.933771+00:00
-- url     : https://prove2.me/theorems/a31e73d4-87ee-41a6-9576-e8c75e375a14
-- title:
--   BDL26 Random Perturbation: grid Point Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Point Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L50-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L50-L55

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.gridPointQuery_cost_le (K : ℕ) (g : Grid K) : (gridPointQuery K g).2 ≤ 3*K+9 := by sorry
