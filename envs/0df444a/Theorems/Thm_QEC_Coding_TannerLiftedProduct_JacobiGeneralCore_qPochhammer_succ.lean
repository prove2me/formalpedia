-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:41.864274+00:00
-- url     : https://prove2.me/theorems/30e64d7b-1a7b-4358-bd1d-65f88a70f9a1
-- title:
--   Jacobi General Core: q Pochhammer succ
-- statement:
--   **Recurrence for q-Pochhammer.** $(a;q)_{n+1} = (a;q)_n \cdot (1 - a q^n)$.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L90-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L90-L92

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_succ [CommRing R] (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by sorry
