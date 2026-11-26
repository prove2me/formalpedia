-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f
-- name    : P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:06.087053+00:00
-- url     : https://prove2.me/theorems/c6c7941a-8f23-4fcc-a8c1-e91b52c8a03b
-- title:
--   P2 M Fixed Order Factor sum char pow eq one  fb05deb8e53f: P2 M Fixed Order Factor sum char pow eq one  fb05deb8e53f
-- statement:
--   **Orthogonality for characters of order dividing `r`.** For a prime `p` with `r ∣ p - 1`,
--   the sum of `χ(a) conj χ(b)` over the characters `χ` modulo `p` with `χʳ = 1` is `r` when
--   `a/b` is a nonzero `r`-th power modulo `p`, and `0` otherwise.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L86-L113
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L86-L113

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

theorem P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f {r : ℕ} (hr : r ∣ p - 1) (a b : ZMod p) (hb : b ≠ 0) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ a * starRingEnd ℂ (χ b) =
      if ∃ c : ZMod p, c ≠ 0 ∧ a = c ^ r * b then (r : ℂ) else 0 := by sorry

alias «FixedOrderFactor».«sum_char_pow_eq_one'» := P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f
