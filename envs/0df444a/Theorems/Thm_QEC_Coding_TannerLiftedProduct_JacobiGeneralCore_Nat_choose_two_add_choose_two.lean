-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_add_choose_two
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.choose_two_add_choose_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:36.217602+00:00
-- url     : https://prove2.me/theorems/ed9061a5-574d-4a86-af22-8021d5a4581c
-- title:
--   Nat: choose two add choose two
-- statement:
--   `C(m+k,2) + C(m,2) + m = C(k,2) + m*(m+k)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L47-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L47-L52

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.choose_two_add_choose_two (m k : ℕ) :
    (m + k).choose 2 + m.choose 2 + m = k.choose 2 + m * (m + k) := by sorry
