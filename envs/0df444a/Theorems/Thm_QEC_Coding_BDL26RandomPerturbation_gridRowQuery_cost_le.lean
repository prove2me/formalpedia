-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridRowQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.gridRowQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:58:37.13597+00:00
-- url     : https://prove2.me/theorems/73cd1a8a-9b38-4432-9971-5d544948c586
-- title:
--   BDL26 Random Perturbation: grid Row Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Row Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L107-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L107-L110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.gridRowQuery_cost_le {K : ℕ} (L : List (GridCoordinate K)) (a b : GridCoordinate K) :
    (gridRowQuery L a b).2 ≤ 4*L.length := by sorry
