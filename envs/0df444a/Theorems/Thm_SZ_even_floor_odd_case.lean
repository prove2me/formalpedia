-- Prove2me | Theorems.Thm_SZ_even_floor_odd_case
-- name    : SZ.even_floor_odd_case
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:12:32.390807+00:00
-- url     : https://prove2.me/theorems/ab6b774d-0250-4151-bfd8-0683fcf44c31
-- title:
--   SZ: even floor odd case
-- statement:
--   Odd `n`: `ξ (√3)^{2s+1} = (2 + y) 3ˢ`, whose floor is even by Lemma D — L1(b) supplies
--   a `bᵢ = 2`, i.e. a `y`-digit `0`, beyond index `s`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L141-L155
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L141-L155

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.even_floor_odd_case (s : ℕ) : Even ⌊witXi * Real.sqrt 3 ^ (2 * s + 1)⌋ := by sorry
