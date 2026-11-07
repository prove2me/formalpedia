-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_choose_two_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.choose_two_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:03.060473+00:00
-- url     : https://prove2.me/theorems/a131d19c-8878-4b8f-9080-5151f149c878
-- title:
--   Nat: choose two succ
-- statement:
--   Pascal's rule specialised to `C(·, 2)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L43-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L43-L44

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat.choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by sorry
