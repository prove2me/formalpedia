-- Prove2me | Theorems.Thm_P2M_BandParity_matching_indep__280075205c52
-- name    : P2M_BandParity_matching_indep__280075205c52
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:56:17.700278+00:00
-- url     : https://prove2.me/theorems/9ac36e4d-2af4-52fd-9d1d-185f7ca1156e
-- title:
--   P2 M Band Parity matching indep  280075205c52: P2 M Band Parity matching indep  280075205c52
-- statement:
--   **Independence of the matching.** Two bijections from `X` onto `Y` give correlations that
--   agree modulo `4`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L61-L65
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L61-L65

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset

theorem P2M_BandParity_matching_indep__280075205c52 {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] := by sorry

alias «BandParity».«matching_indep'» := P2M_BandParity_matching_indep__280075205c52
