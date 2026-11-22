-- Prove2me | Theorems.Thm_SZ_oneAddSqrtThree_mem_MahlerZ
-- name    : SZ.oneAddSqrtThree_mem_MahlerZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:51:10.018108+00:00
-- url     : https://prove2.me/theorems/a7576697-34dc-42f7-ba95-f655ef421806
-- title:
--   SZ: one Add Sqrt Three mem Mahler Z
-- statement:
--   **[Dub06EO] Theorem 1(iv) at `α = 1 + √3`.**  Every `⌊(1+√3)ⁿ/3⌋` is even, so
--   `1 + √3 ∈ 𝒵`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L123-L128
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L123-L128

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
set_option autoImplicit false
open SZ
open Real

theorem SZ.oneAddSqrtThree_mem_MahlerZ : (1 + Real.sqrt 3) ∈ MahlerZ := by sorry
