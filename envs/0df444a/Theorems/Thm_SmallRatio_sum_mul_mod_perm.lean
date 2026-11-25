-- Prove2me | Theorems.Thm_SmallRatio_sum_mul_mod_perm
-- name    : SmallRatio.sum_mul_mod_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:43.891211+00:00
-- url     : https://prove2.me/theorems/afc62d8e-bcfc-51c0-9f8f-960733349128
-- title:
--   Small Ratio: sum mul mod perm
-- statement:
--   Multiplication by a unit permutes `range k`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L54-L72
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L54-L72

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.sum_mul_mod_perm {M : Type*} [AddCommMonoid M] (h k : ℕ) (hk : 0 < k) (hc : Nat.Coprime h k)
    (f : ℕ → M) : ∑ r ∈ range k, f (h * r % k) = ∑ r ∈ range k, f r := by sorry
