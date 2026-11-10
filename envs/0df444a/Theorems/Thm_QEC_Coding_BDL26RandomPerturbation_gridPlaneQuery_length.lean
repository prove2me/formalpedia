-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridPlaneQuery_length
-- name    : QEC.Coding.BDL26RandomPerturbation.gridPlaneQuery_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:14:16.134871+00:00
-- url     : https://prove2.me/theorems/9274b0e4-4621-432a-b7a0-cb08ce5fc32c
-- title:
--   BDL26 Random Perturbation: grid Plane Query length
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Plane Query length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L95-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L95-L99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.gridPlaneQuery_length {K : ℕ} (L : List (GridCoordinate K)) (a : GridCoordinate K) :
    (gridPlaneQuery L a).1.length = L.length^2 := by sorry
