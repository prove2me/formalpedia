-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:09.9796+00:00
-- url     : https://prove2.me/theorems/3c104d26-77d2-4497-b548-70af66c4bb24
-- title:
--   Jacobi General Core: q Pochhammer zero
-- statement:
--   The empty q-Pochhammer product $(a;q)_0 = 1$.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L86-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L86-L87

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
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero [CommRing R] (a q : R) : qPochhammer a q 0 = 1 := by sorry
