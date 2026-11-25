-- Prove2me | Theorems.Thm_SZ_even_floor_even_case
-- name    : SZ.even_floor_even_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:12:41.29924+00:00
-- url     : https://prove2.me/theorems/e6f29792-4e51-4343-b043-2d378d853a0c
-- title:
--   SZ: even floor even case
-- statement:
--   Even `n`: `ξ (√3)^{2(s+1)} = (4 + x) 3ˢ`, whose floor is even by Lemma D — the `aᵢ`
--   are all even, and L1(a) supplies a `0` beyond index `s`, so the digits are canonical.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L127-L137
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L127-L137

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.even_floor_even_case (s : ℕ) : Even ⌊witXi * Real.sqrt 3 ^ (2 * (s + 1))⌋ := by sorry
