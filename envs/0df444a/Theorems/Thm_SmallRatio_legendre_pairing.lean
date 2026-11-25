-- Prove2me | Theorems.Thm_SmallRatio_legendre_pairing
-- name    : SmallRatio.legendre_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:21:31.308815+00:00
-- url     : https://prove2.me/theorems/ad0657d4-a33c-5e4c-bc31-bda6e7910acd
-- title:
--   Small Ratio: legendre pairing
-- statement:
--   **Legendre's pairing.**
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Legendre.lean#L52-L244
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Legendre.lean#L52-L244

module
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_Legendre
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
set_option maxHeartbeats 1000000

theorem SmallRatio.legendre_pairing (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : Nat.Coprime u v)
    (hsmall : 2 * u * v < k) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hcong : (k : ℤ) ∣ (h : ℤ) * v - ε * u) :
    ∃ j ∈ Icc 1 (steps k h), rem k h j = u ∧ den k h j = v ∧ ε = (-1) ^ (j + 1) := by sorry
