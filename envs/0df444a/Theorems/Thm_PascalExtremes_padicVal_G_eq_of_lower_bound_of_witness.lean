-- Prove2me | Theorems.Thm_PascalExtremes_padicVal_G_eq_of_lower_bound_of_witness
-- name    : PascalExtremes.padicVal_G_eq_of_lower_bound_of_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:25.416314+00:00
-- url     : https://prove2.me/theorems/96b11f9e-6c90-4222-b91a-6c2d706d234d
-- title:
--   Pascal Extremes: padic Val G eq of lower bound of witness
-- statement:
--   If every selected coefficient has valuation at least `r` and one selected
--   coefficient has valuation exactly `r`, then the restricted gcd does too.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L88-L124
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L88-L124

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.padicVal_G_eq_of_lower_bound_of_witness
    {N m p r : ℕ} (hm : 0 < m) (hNm : m < N) (hp : p.Prime)
    (hlower :
      ∀ k, Admissible N m k → r ≤ padicValNat p (N.choose k))
    (hwitness :
      ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = r) :
    padicValNat p (G N m) = r := by sorry
