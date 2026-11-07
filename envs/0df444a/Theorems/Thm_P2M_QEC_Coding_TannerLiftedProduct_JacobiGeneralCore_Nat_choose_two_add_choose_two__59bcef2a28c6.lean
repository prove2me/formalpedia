-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two__59bcef2a28c6
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two__59bcef2a28c6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:08.811675+00:00
-- url     : https://prove2.me/theorems/6fc41cb4-6222-4557-82df-71089ef4bb37
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi General Core Nat choose two add choose two  59bcef2a28c6: P2 M QEC Coding Tanner Lifted Product Jacobi General Core Nat choose two add choose two  59bcef2a
-- statement:
--   `C(n,2) + C(n+l+1,2) + (n+l+1) = C(l+2,2) + n*(n+l+1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L55-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L55-L60

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two__59bcef2a28c6 (n l : ℕ) :
    n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1)) =
    (l + 2).choose 2 + n * (n + (l + 1)) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiGeneralCore».«Nat».«choose_two_add_choose_two'» := P2M_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two__59bcef2a28c6
