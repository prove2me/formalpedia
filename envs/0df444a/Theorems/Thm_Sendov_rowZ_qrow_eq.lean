-- Prove2me | Theorems.Thm_Sendov_rowZ_qrow_eq
-- name    : Sendov.rowZ_qrow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:19.824479+00:00
-- url     : https://prove2.me/theorems/361979dd-03fe-44eb-8fdd-ce632b18e677
-- title:
--   Sendov: row Z qrow eq
-- statement:
--   Reading the packed row back, given the overflow bound on the packed coefficients.  The
--   bound is a hypothesis: it is discharged per degree from explicit numerical parameters.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L80-L86
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L80-L86

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.rowZ_qrow_eq (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) (hτ : 0 < τ)
    (hbound : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ) :
    unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)
      = rowZ (qrow g₀ g₁ g₂ k) β := by sorry
