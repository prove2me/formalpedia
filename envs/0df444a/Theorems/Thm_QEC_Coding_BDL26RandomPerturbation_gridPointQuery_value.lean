-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridPointQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.gridPointQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:57:25.986142+00:00
-- url     : https://prove2.me/theorems/5238b914-90fa-4518-9fab-5c3247a19192
-- title:
--   BDL26 Random Perturbation: grid Point Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the grid Point Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L37-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean#L37-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.gridPointQuery_value (K : ℕ) (g : Grid K) : (gridPointQuery K g).1 = gridPoint K g := by sorry
