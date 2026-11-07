-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_mul
-- name    : QEC.Coding.BDL26RandomPerturbation.lllWeight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:40.127196+00:00
-- url     : https://prove2.me/theorems/db123ddc-ad8c-4cc3-b60d-afb616d6b70f
-- title:
--   BDL26 Random Perturbation: lll Weight mul
-- statement:
--   The BDL26 Random Perturbation construction uses the lll Weight mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean#L21-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean#L21-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.lllWeight_mul (D : ℕ) : 2*((D : ℝ)+1)*lllWeight D = 1 := by sorry
