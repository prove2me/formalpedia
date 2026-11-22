-- Prove2me | Theorems.Thm_SZ_quadPisot_mem_MahlerZ
-- name    : SZ.quadPisot_mem_MahlerZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:29.207746+00:00
-- url     : https://prove2.me/theorems/d3e94c03-cf42-4d45-b7c9-6710cd362d94
-- title:
--   SZ: quad Pisot mem Mahler Z
-- statement:
--   **Theorem B (the `𝒵` half).**  Every quadratic Pisot number other than the golden mean
--   lies in `𝒵`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Classification.lean#L82-L129
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Classification.lean#L82-L129

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
set_option autoImplicit false
open SZ
open Real

theorem SZ.quadPisot_mem_MahlerZ {α : ℝ} (h : IsQuadPisot α) (hne : α ≠ golden) :
    α ∈ MahlerZ := by sorry
