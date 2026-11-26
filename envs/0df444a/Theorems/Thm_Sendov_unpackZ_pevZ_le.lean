-- Prove2me | Theorems.Thm_Sendov_unpackZ_pevZ_le
-- name    : Sendov.unpackZ_pevZ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:50.536912+00:00
-- url     : https://prove2.me/theorems/00bc3bca-6473-4782-9682-6a1af7922f85
-- title:
--   Sendov: unpack Z pev Z le
-- statement:
--   The round trip, tolerating extra room: unpacking to length `m ≥ p.length` returns `p`
--   zero-padded.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L330-L358
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L330-L358

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.unpackZ_pevZ_le (β : ℤ) (hβ : 0 < β) :
    ∀ (m : ℕ) (p : List ℤ), p.length ≤ m → (∀ a ∈ p, 2 * |a| < β) →
      unpackZ β m (pevZ p β) = p ++ List.replicate (m - p.length) 0 := by sorry
