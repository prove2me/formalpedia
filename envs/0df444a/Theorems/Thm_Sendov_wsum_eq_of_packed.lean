-- Prove2me | Theorems.Thm_Sendov_wsum_eq_of_packed
-- name    : Sendov.wsum_eq_of_packed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:06.803294+00:00
-- url     : https://prove2.me/theorems/55cdad4b-62c8-567e-bfdb-b2a531856408
-- title:
--   Sendov: wsum eq of packed
-- statement:
--   **Verification of a supplied moment numerator.**  Given the overflow bounds, checking a
--   generator-supplied `Nmom` is one integer comparison against the packed computation — which is
--   a single exponentiation and `2k+1` digit extractions.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L406-L416
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L406-L416

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.wsum_eq_of_packed (g₀ g₁ g₂ : List ℤ) (k : ℕ) (L β τ : ℤ) (Nmom : List ℤ)
    (hβ : 0 < β) (hτ : 0 < τ)
    (hbτ : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ)
    (hbN : ∀ a ∈ Nmom, 2 * |a| < β)
    (hbW : ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β)
    (hlen : Nmom.length = (wsum L 0 (qrow g₀ g₁ g₂ k)).length)
    (hcheck : wsumZ L 0 (unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)) = pevZ Nmom β) :
    Nmom = wsum L 0 (qrow g₀ g₁ g₂ k) := by sorry
