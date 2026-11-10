-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridListQuery_length
-- name    : QEC.Coding.BDL26RandomPerturbation.gridListQuery_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:10:20.35242+00:00
-- url     : https://prove2.me/theorems/299c3af6-3eb9-46ec-a56a-732b9b96aceb
-- title:
--   BDL26 Random Perturbation: grid List Query length
-- statement:
--   The BDL26 Random Perturbation construction uses the grid List Query length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L101-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L101-L105

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.gridListQuery_length (K : ℕ) : (gridListQuery K).1.length = (2*K+1)^3 := by sorry
