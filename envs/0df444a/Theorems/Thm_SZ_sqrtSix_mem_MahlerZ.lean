-- Prove2me | Theorems.Thm_SZ_sqrtSix_mem_MahlerZ
-- name    : SZ.sqrtSix_mem_MahlerZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:09.872493+00:00
-- url     : https://prove2.me/theorems/8beb29b9-13c2-40e5-9bfc-311cb295d183
-- title:
--   SZ: sqrt Six mem Mahler Z
-- statement:
--   `√6 ∈ 𝒵`, with the translate `j = 3`, `k₀ = 1`: `σ = 2.8√6 - 6 = 0.858…`  Here
--   `e = m - 2`, so tail hygiene is not needed.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L158-L170
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L158-L170

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
set_option autoImplicit false
open SZ

theorem SZ.sqrtSix_mem_MahlerZ : Real.sqrt 6 ∈ MahlerZ := by sorry
