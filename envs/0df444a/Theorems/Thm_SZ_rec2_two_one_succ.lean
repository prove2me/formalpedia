-- Prove2me | Theorems.Thm_SZ_rec2_two_one_succ
-- name    : SZ.rec2_two_one_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:48:50.001814+00:00
-- url     : https://prove2.me/theorems/af3caf6b-01b4-42ca-bb9a-9410fa70bf90
-- title:
--   SZ: rec2 two one succ
-- statement:
--   The design's trace sequence at `(a,b) = (2,1)` is the Pell sequence shifted by one,
--   with the convention `P₋₁ = 1` supplied by the seed.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L76-L82
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L76-L82

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.rec2_two_one_succ (n : ℕ) : rec2 2 1 1 0 (n + 1) = pell n := by sorry
