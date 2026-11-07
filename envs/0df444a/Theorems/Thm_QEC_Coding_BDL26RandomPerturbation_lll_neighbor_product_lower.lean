-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lll_neighbor_product_lower
-- name    : QEC.Coding.BDL26RandomPerturbation.lll_neighbor_product_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:40.150977+00:00
-- url     : https://prove2.me/theorems/abf0b843-45ca-4f8d-9e11-912e1dcf2ed9
-- title:
--   BDL26 Random Perturbation: lll neighbor product lower
-- statement:
--   Bernoulli gives a uniform positive lower bound for the entire neighbor product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean#L27-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean#L27-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.lll_neighbor_product_lower {I : Type*} (D : ℕ) (s : Finset I)
    (hcard : s.card ≤ D) :
    (1/2 : ℝ) ≤ ∏ _i ∈ s, (1-lllWeight D) := by sorry
