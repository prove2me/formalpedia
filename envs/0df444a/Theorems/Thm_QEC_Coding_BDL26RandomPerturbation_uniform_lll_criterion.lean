-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_uniform_lll_criterion
-- name    : QEC.Coding.BDL26RandomPerturbation.uniform_lll_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:45:33.092621+00:00
-- url     : https://prove2.me/theorems/2203f22b-6044-4a6c-8da4-44c908ca34fc
-- title:
--   BDL26 Random Perturbation: uniform lll criterion
-- statement:
--   The actual degree and probability bounds can be substituted directly into this criterion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean#L42-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean#L42-L55

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.uniform_lll_criterion {I : Type*} (D : ℕ) (s : Finset I)
    (hcard : s.card ≤ D) {p : ℝ} (hp : p ≤ 1/(4*((D : ℝ)+1))) :
    p ≤ lllWeight D * ∏ _i ∈ s, (1-lllWeight D) := by sorry
