-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_intRealQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.intRealQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:36:34.293227+00:00
-- url     : https://prove2.me/theorems/14745d6e-bad8-409a-a00e-f5219e8109b3
-- title:
--   BDL26 Random Perturbation: int Real Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the int Real Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L25-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L25-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.intRealQuery_value (z : ℤ) : (intRealQuery z).1 = (z : ℝ) := by sorry
