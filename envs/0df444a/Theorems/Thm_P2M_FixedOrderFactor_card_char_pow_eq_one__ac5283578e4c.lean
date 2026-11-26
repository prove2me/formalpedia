-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_card_char_pow_eq_one__ac5283578e4c
-- name    : P2M_FixedOrderFactor_card_char_pow_eq_one__ac5283578e4c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:26.729501+00:00
-- url     : https://prove2.me/theorems/ad3844fe-4c90-4cc3-8d65-330c9bc8a808
-- title:
--   P2 M Fixed Order Factor card char pow eq one  ac5283578e4c: P2 M Fixed Order Factor card char pow eq one  ac5283578e4c
-- statement:
--   There are exactly `r` characters modulo `p` with `χʳ = 1` when `r ∣ p - 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L117-L123
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L117-L123

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

theorem P2M_FixedOrderFactor_card_char_pow_eq_one__ac5283578e4c {r : ℕ} (hr : r ∣ p - 1) :
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1)).card = r := by sorry

alias «FixedOrderFactor».«card_char_pow_eq_one'» := P2M_FixedOrderFactor_card_char_pow_eq_one__ac5283578e4c
