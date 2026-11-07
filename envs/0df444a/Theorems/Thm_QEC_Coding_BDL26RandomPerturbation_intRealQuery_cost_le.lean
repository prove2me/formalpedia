-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_intRealQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.intRealQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:37:02.185166+00:00
-- url     : https://prove2.me/theorems/a2a72046-c04e-493d-9152-1c205f919429
-- title:
--   BDL26 Random Perturbation: int Real Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the int Real Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L28-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L28-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.intRealQuery_cost_le (z : ℤ) : (intRealQuery z).2 ≤ z.natAbs+2 := by sorry
