-- Prove2me | Theorems.Thm_SZ_mem_MahlerZ_of_three_le
-- name    : SZ.mem_MahlerZ_of_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:50:37.920289+00:00
-- url     : https://prove2.me/theorems/934c90ec-52be-4508-9570-83a91e07f3d3
-- title:
--   SZ: mem Mahler Z of three le
-- statement:
--   **[Dub06EO] Theorem 1(i)** (Tijdeman).  Every real `α ≥ 3` lies in `𝒵`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L155-L160
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L155-L160

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.mem_MahlerZ_of_three_le (hα : 3 ≤ α) : α ∈ MahlerZ := by sorry
