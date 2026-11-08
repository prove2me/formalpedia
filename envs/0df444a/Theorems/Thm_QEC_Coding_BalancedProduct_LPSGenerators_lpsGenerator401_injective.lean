-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGenerator401_injective
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerator401_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:28.001563+00:00
-- url     : https://prove2.me/theorems/a13935f4-a958-46f9-b585-06aa32997022
-- title:
--   LPSGenerators: lps Generator401 injective
-- statement:
--   Under the source size condition `q > 2√401` (used here through its
--   integer consequence `q > 40`), distinct normalized shell elements remain
--   distinct even after projectivization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L395-L455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L395-L455

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic

theorem QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerator401_injective
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Function.Injective
      (fun t : {t // t ∈ shell401} => lpsGenerator401 q hq t.1 t.2) := by sorry
