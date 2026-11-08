-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_shellIndex401_eq_of_lpsMatrix401_eq
-- name    : QEC.Coding.BalancedProduct.LPSGenerators.shellIndex401_eq_of_lpsMatrix401_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:51:22.443209+00:00
-- url     : https://prove2.me/theorems/be1ea3f2-6269-4ddf-8d6d-9602cac05103
-- title:
--   LPSGenerators: shell Index401 eq of lps Matrix401 eq
-- statement:
--   For `q > 40`, the integral quaternion representation has no collisions
--   after reduction modulo `q`.  This is the coordinate-injectivity half of the
--   later projective generator count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L218-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean#L218-L287

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

theorem QEC.Coding.BalancedProduct.LPSGenerators.shellIndex401_eq_of_lpsMatrix401_eq
    (q : ℕ) [Fact q.Prime] (hq : 40 < q)
    {t u : ShellIndex401}
    (hM : lpsMatrix401 q t = lpsMatrix401 q u) : t = u := by sorry
