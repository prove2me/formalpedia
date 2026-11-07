-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_lt_choose_two_of_add_two_le
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:58.752412+00:00
-- url     : https://prove2.me/theorems/6551698c-4d93-4710-a4c0-2dcf786061b6
-- title:
--   Nat: lt choose two of add two le
-- statement:
--   `C(k,2)` eventually dominates: `d < C(k,2)` as soon as `d + 2 ≤ k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L69-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L69-L71

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le {d k : ℕ} (hk : d + 2 ≤ k) : d < k.choose 2 := by sorry
