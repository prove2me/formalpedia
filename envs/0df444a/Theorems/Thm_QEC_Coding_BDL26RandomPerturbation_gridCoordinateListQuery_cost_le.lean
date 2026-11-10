-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridCoordinateListQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.gridCoordinateListQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:58:47.641785+00:00
-- url     : https://prove2.me/theorems/e30060c1-39b0-4b29-b4b1-4b8970c9b22b
-- title:
--   BDL26 Random Perturbation: grid Coordinate List Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Coordinate List Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L62-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L62-L69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.gridCoordinateListQuery_cost_le (K : ℕ) :
    (gridCoordinateListQuery K).2 ≤ 2*(2*K+1)^2+4*(2*K+1)+1 := by sorry
