-- Prove2me | Theorems.Thm_SZ_sqrtThree_mem_MahlerZ
-- name    : SZ.sqrtThree_mem_MahlerZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:30:34.266202+00:00
-- url     : https://prove2.me/theorems/56904200-c366-4f80-8456-bbd123e3260e
-- title:
--   SZ: sqrt Three mem Mahler Z
-- statement:
--   **[Dub06EO] Problem 3, answered: `√3 ∈ 𝒵`.**  There is a nonzero real `ξ` — the
--   explicit `witXi = 1.3416089979611266516309894306526154258451…` built by the cover greedy
--   — with `⌊ξ (√3)ⁿ⌋` even for every `n ≥ 1`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L166-L176
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean#L166-L176

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
set_option autoImplicit false
open SZ

theorem SZ.sqrtThree_mem_MahlerZ : Real.sqrt 3 ∈ MahlerZ := by sorry
