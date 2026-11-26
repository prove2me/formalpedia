-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_model_pair_average__85ab05e3a191
-- name    : P2M_FixedOrderFactor_model_pair_average__85ab05e3a191
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:34.716171+00:00
-- url     : https://prove2.me/theorems/0cacaa7d-39ac-5a19-9f7c-1c9c52cf9a58
-- title:
--   P2 M Fixed Order Factor model pair average  85ab05e3a191: P2 M Fixed Order Factor model pair average  85ab05e3a191
-- statement:
--   **The model keeps exactly the `r`-th power ratios.** If `z_q` are independent and uniform on
--   the `r`-th roots of unity, then `E[z^m conj(z^n)]` is `1` when `m/n` is the `r`-th power of a
--   rational number and `0` otherwise (for `m, n ≥ 1` whose prime factors lie in `S`).
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L123-L139
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L123-L139

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
open Classical

theorem P2M_FixedOrderFactor_model_pair_average__85ab05e3a191 {r : ℕ} (hr : 0 < r) (S : Finset Nat.Primes) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (1 / (r : ℂ) ^ S.card) * ∑ j : S → Fin r, zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      if ∃ x : ℚ, (m : ℚ) / n = x ^ r then 1 else 0 := by sorry

alias «FixedOrderFactor».«model_pair_average'» := P2M_FixedOrderFactor_model_pair_average__85ab05e3a191
