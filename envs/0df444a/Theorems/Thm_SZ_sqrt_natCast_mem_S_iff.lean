-- Prove2me | Theorems.Thm_SZ_sqrt_natCast_mem_S_iff
-- name    : SZ.sqrt_natCast_mem_S_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:36:31.516048+00:00
-- url     : https://prove2.me/theorems/b73d5a20-2a67-4cd3-90ef-e32790341f23
-- title:
--   SZ: sqrt nat Cast mem S iff
-- statement:
--   **Theorem B.**  For an integer `m ≥ 2`, `√m ∈ 𝒮` if and only if `m = 2`.  Both
--   directions are proved from scratch in this directory, so the statement carries no
--   citation.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L236-L242
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Cells.lean#L236-L242

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
set_option autoImplicit false
open SZ

theorem SZ.sqrt_natCast_mem_S_iff {m : ℕ} (hm : 2 ≤ m) : Real.sqrt m ∈ S ↔ m = 2 := by sorry
