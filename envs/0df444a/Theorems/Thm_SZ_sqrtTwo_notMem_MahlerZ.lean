-- Prove2me | Theorems.Thm_SZ_sqrtTwo_notMem_MahlerZ
-- name    : SZ.sqrtTwo_notMem_MahlerZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:55.421107+00:00
-- url     : https://prove2.me/theorems/e2f02fd1-5fa9-412e-968f-fdfed6d1db86
-- title:
--   SZ: sqrt Two not Mem Mahler Z
-- statement:
--   **`√2 ∉ 𝒵`.**  A witness would make both `2ξ` and `√2 ξ` even integers, hence
--   `√2` rational.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L161-L187
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtTwo.lean#L161-L187

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
set_option autoImplicit false
open SZ

theorem SZ.sqrtTwo_notMem_MahlerZ : Real.sqrt 2 ∉ MahlerZ := by sorry
