-- Prove2me | Theorems.Thm_PascalMinusOne_padicVal_G_eq_of_lower_bound_of_witness
-- name    : PascalMinusOne.padicVal_G_eq_of_lower_bound_of_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:02.419203+00:00
-- url     : https://prove2.me/theorems/3dc481d7-9b51-47d6-8427-446111e64712
-- title:
--   Pascal Minus One: padic Val G eq of lower bound of witness
-- statement:
--   If every admissible binomial coefficient has `p`-adic valuation at least `r`,
--   and one admissible coefficient has valuation exactly `r`, then the restricted gcd
--   has valuation exactly `r`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L46-L82
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean#L46-L82

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.padicVal_G_eq_of_lower_bound_of_witness
    {N m p r : ℕ} (hm : 0 < m) (hNm : m < N) (hp : p.Prime)
    (hlower :
      ∀ k, Admissible N m k → r ≤ padicValNat p (N.choose k))
    (hwitness :
      ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = r) :
    padicValNat p (G N m) = r := by sorry
