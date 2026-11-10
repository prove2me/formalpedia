-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridListQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.gridListQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:10:52.296597+00:00
-- url     : https://prove2.me/theorems/55d73bde-45e6-4e76-924a-ed779a55caff
-- title:
--   BDL26 Random Perturbation: grid List Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the grid List Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L119-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L119-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.gridListQuery_cost_le (K : ℕ) :
    (gridListQuery K).2 ≤ 6*(2*K+1)^3+3*(2*K+1)^2+5*(2*K+1)+1 := by sorry
