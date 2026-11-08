-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGenerators401_ne_conj_upperUnipotent
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerators401_ne_conj_upperUnipotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:50.873433+00:00
-- url     : https://prove2.me/theorems/f08d3532-2a76-4b3e-8740-03cca51cfac6
-- title:
--   LPSGenerators: lps Generators401 ne conj upper Unipotent
-- statement:
--   The determinant proof closes the source quotient condition at the level
--   of concrete generators: no generator lies in any conjugate of the
--   upper-unipotent subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L521-L529
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L521-L529

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerators401_ne_conj_upperUnipotent
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq)
    (g : PGL(2, ZMod q)) (x : ZMod q) :
    s ≠ g * upperUnipotentPGL x * g⁻¹ := by sorry
