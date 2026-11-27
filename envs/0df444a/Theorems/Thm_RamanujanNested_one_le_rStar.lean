-- Prove2me | Theorems.Thm_RamanujanNested_one_le_rStar
-- name    : RamanujanNested.one_le_rStar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:49.985824+00:00
-- url     : https://prove2.me/theorems/19df3e0c-be34-4dbe-b399-d5f8128e11c0
-- title:
--   Ramanujan Nested: one le r Star
-- statement:
--   `r* ≥ 1` whenever `A ≥ 0` — needed to justify the canonical seed `T = 1`
--   sits inside `[0, r*]`. `rStar_sq` gives `r*² = 1 + A r* ≥ 1`, so `r* ≥ 1` since
--   `r* ≥ 0`.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Bounds.lean#L64-L71
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Bounds.lean#L64-L71

module
public import Definitions.Def_RamanujanNested_Defs
public import Definitions.Def_RamanujanNested_Bounds
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.one_le_rStar {A : ℝ} (hA : 0 ≤ A) : 1 ≤ rStar A := by sorry
