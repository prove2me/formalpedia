-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_le_choose_two_add_one
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.le_choose_two_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:39.497914+00:00
-- url     : https://prove2.me/theorems/05b083a4-53a5-4625-8819-514f15a1185c
-- title:
--   Nat: le choose two add one
-- statement:
--   `C(k,2)` is at least `k - 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L63-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L63-L66

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.le_choose_two_add_one (k : ℕ) : k ≤ k.choose 2 + 1 := by sorry
