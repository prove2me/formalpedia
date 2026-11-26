-- Prove2me | Theorems.Thm_P2M_BandParity_matching__4d040604aa82
-- name    : P2M_BandParity_matching__4d040604aa82
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:47.180055+00:00
-- url     : https://prove2.me/theorems/210f77bf-0b7a-5f69-b496-2c6f0a78d8a4
-- title:
--   P2 M Band Parity matching  4d040604aa82: P2 M Band Parity matching  4d040604aa82
-- statement:
--   **The matching lemma.** For a bijection `π` from `X` onto `Y` and sign functions `σ` on `X`
--   and `τ` on `Y`, `∑_{x ∈ X} σ(x) τ(π x) ≡ ∑_X σ + ∑_Y τ - |X| (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L47-L57
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L47-L57

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset

theorem P2M_BandParity_matching__4d040604aa82 {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π : ι → κ)
    (hπ : Set.BijOn π X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x + ∑ y ∈ Y, τ y - X.card [ZMOD 4] := by sorry

alias «BandParity».«matching'» := P2M_BandParity_matching__4d040604aa82
