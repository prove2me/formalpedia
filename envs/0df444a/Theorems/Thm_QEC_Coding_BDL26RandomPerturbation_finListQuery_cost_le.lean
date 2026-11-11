-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_finListQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.finListQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:58:11.590347+00:00
-- url     : https://prove2.me/theorems/436e54dc-9641-4fb7-a9be-00caaab88b9c
-- title:
--   BDL26 Random Perturbation: fin List Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the fin List Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L27-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L27-L35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.finListQuery_cost_le (n : ℕ) : (finListQuery n).2 ≤ 2*n^2+1 := by sorry
