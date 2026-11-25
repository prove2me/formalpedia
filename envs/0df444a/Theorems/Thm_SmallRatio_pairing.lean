-- Prove2me | Theorems.Thm_SmallRatio_pairing
-- name    : SmallRatio.pairing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:25:12.064679+00:00
-- url     : https://prove2.me/theorems/3786e299-bd25-4f64-a376-8ee224181314
-- title:
--   Small Ratio: pairing
-- statement:
--   **Legendre's pairing** (manuscript, Lemma 5.13). If `u, v ≥ 1` are coprime, `uv < k/2` and
--   `hv ≡ εu (mod k)` with `ε = ±1`, then `(u, v) = (r_j, q_{j-1})` and `ε = (-1)^{j+1}` for some `1 ≤ j ≤ n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L61-L65
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L61-L65

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.pairing {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
    (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : Nat.Coprime u v) (hsmall : 2 * u * v < k)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hcong : (k : ℤ) ∣ (h : ℤ) * v - ε * u) :
    ∃ j ∈ Icc 1 (steps k h), rem k h j = u ∧ den k h j = v ∧ ε = (-1) ^ (j + 1) := by sorry
