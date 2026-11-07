-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_prod_one_add_mul_pow_eq_sum_qBinom
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.prod_one_add_mul_pow_eq_sum_qBinom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:20.708198+00:00
-- url     : https://prove2.me/theorems/9e17848a-a785-4c7b-bec0-92f848d34ba2
-- title:
--   Jacobi General Core: prod one add mul pow eq sum q Binom
-- statement:
--   **Finite q-binomial theorem.**
--   $$\prod_{k=0}^{n-1}(1 + z q^k) = \sum_{k=0}^{n} q^{\binom{k}{2}} \binom{n}{k}_q z^k.$$
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FiniteBinomial.lean#L31-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FiniteBinomial.lean#L31-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
set_option autoImplicit false
open Finset Filter
open scoped Topology
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.prod_one_add_mul_pow_eq_sum_qBinom [CommRing R] (q z : R) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + z * q ^ k)
      = ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k := by sorry
