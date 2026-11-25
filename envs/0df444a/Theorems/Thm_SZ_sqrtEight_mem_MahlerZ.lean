-- Prove2me | Theorems.Thm_SZ_sqrtEight_mem_MahlerZ
-- name    : SZ.sqrtEight_mem_MahlerZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:13:12.652243+00:00
-- url     : https://prove2.me/theorems/c414819f-cb81-58c8-9350-512f8bf034ce
-- title:
--   SZ: sqrt Eight mem Mahler Z
-- statement:
--   `√8 ∈ 𝒵`, with the translate `j = 3`, `k₀ = 1`: `σ = (20/7)√8 - 6 = 2.081…`  Here
--   `e = m - 2`, so tail hygiene is not needed.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L190-L202
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L190-L202

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
set_option autoImplicit false
open SZ

theorem SZ.sqrtEight_mem_MahlerZ : Real.sqrt 8 ∈ MahlerZ := by sorry
