-- Prove2me | Theorems.Thm_Sendov_pev_wsum_eq_of_packed
-- name    : Sendov.pev_wsum_eq_of_packed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:03:28.164808+00:00
-- url     : https://prove2.me/theorems/e72da500-fd51-5a79-96a6-3aadc9b9dca3
-- title:
--   Sendov: pev wsum eq of packed
-- statement:
--   **Pad-tolerant verification.**  Concludes equality of the polynomial *functions*, which
--   is all the moment needs, and so requires only length *bounds* rather than an exact match.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L580-L596
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L580-L596

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pev_wsum_eq_of_packed (g₀ g₁ g₂ : List ℤ) (k m : ℕ) (L β τ : ℤ) (Nmom : List ℤ)
    (hβ : 0 < β) (hτ : 0 < τ)
    (hbτ : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ)
    (hbN : ∀ a ∈ Nmom, 2 * |a| < β)
    (hbW : ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β)
    (hlenN : Nmom.length ≤ m)
    (hlenW : (wsum L 0 (qrow g₀ g₁ g₂ k)).length ≤ m)
    (hcheck : wsumZ L 0 (unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)) = pevZ Nmom β)
    (α : ℝ) :
    pev Nmom α = pev (wsum L 0 (qrow g₀ g₁ g₂ k)) α := by sorry
