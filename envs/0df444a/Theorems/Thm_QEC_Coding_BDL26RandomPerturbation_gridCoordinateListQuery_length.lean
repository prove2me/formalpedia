-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridCoordinateListQuery_length
-- name    : QEC.Coding.BDL26RandomPerturbation.gridCoordinateListQuery_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:12:23.516697+00:00
-- url     : https://prove2.me/theorems/7bfb46d7-79a3-49e1-b355-bd8d3c784104
-- title:
--   BDL26 Random Perturbation: grid Coordinate List Query length
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Coordinate List Query length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L48-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L48-L49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.gridCoordinateListQuery_length (K : ℕ) : (gridCoordinateListQuery K).1.length = 2*K+1 := by sorry
