-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_char_all__ce659e42cafe
-- name    : P2M_FixedOrderFactor_sum_char_all__ce659e42cafe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:37.320238+00:00
-- url     : https://prove2.me/theorems/1bdd72ad-e646-4992-baa5-a6aba358db53
-- title:
--   P2 M Fixed Order Factor sum char all  ce659e42cafe: P2 M Fixed Order Factor sum char all  ce659e42cafe
-- statement:
--   The full family, for contrast: summed over all characters modulo `p`, `χ(m) conj χ(n)`
--   vanishes unless `m ≡ n (mod p)`; for `m ≠ n` below `p` it vanishes.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L156-L172
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L156-L172

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]

theorem P2M_FixedOrderFactor_sum_char_all__ce659e42cafe {m n : ℕ} (hmn : m ≠ n) (hm : m < p) (hn : n < p) (hn0 : n ≠ 0) :
    ∑ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) = 0 := by sorry

alias «FixedOrderFactor».«sum_char_all'» := P2M_FixedOrderFactor_sum_char_all__ce659e42cafe
