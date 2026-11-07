-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_mul_qPochhammer_mul_qPochhammer
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_mul_qPochhammer_mul_qPochhammer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:18.074123+00:00
-- url     : https://prove2.me/theorems/bb42acc9-45c0-40ec-a845-3c67f2159ed4
-- title:
--   Jacobi General Core: q Binom mul q Pochhammer mul q Pochhammer
-- statement:
--   **Closed-form identity.**
--   For $k \leq n$: $\binom{n}{k}_q (q;q)_k (q;q)_{n-k} = (q;q)_n$.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L147-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean#L147-L174

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_mul_qPochhammer_mul_qPochhammer [CommRing R] (q : R) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom n k q * qPochhammer q q k * qPochhammer q q (n - k)
        = qPochhammer q q n := by sorry
