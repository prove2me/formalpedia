-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_char_pow_eq_one_of_pow__9a04af0fa11c
-- name    : P2M_FixedOrderFactor_sum_char_pow_eq_one_of_pow__9a04af0fa11c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:22.374073+00:00
-- url     : https://prove2.me/theorems/106cbcd1-a8df-5ecf-829c-64be65201638
-- title:
--   P2 M Fixed Order Factor sum char pow eq one of pow  9a04af0fa11c: P2 M Fixed Order Factor sum char pow eq one of pow  9a04af0fa11c
-- statement:
--   If `m = d aʳ` and `n = d bʳ` and `p ∤ m n`, every character of order dividing `r` modulo `p`
--   has `χ(m) conj χ(n) = 1`, so these pairs survive the average over the family.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L128-L152
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L128-L152

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
open Classical

theorem P2M_FixedOrderFactor_sum_char_pow_eq_one_of_pow__9a04af0fa11c {r : ℕ} (hr : r ∣ p - 1) {m n d a b : ℕ}
    (hm : m = d * a ^ r) (hn : n = d * b ^ r) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ m * starRingEnd ℂ (χ n) = r := by sorry

alias «FixedOrderFactor».«sum_char_pow_eq_one_of_pow'» := P2M_FixedOrderFactor_sum_char_pow_eq_one_of_pow__9a04af0fa11c
