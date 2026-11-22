-- Prove2me | Theorems.Thm_SZ_pell_add_two
-- name    : SZ.pell_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:48:43.092865+00:00
-- url     : https://prove2.me/theorems/dea89d00-8061-4acf-ab36-d0ad4df7d9ee
-- title:
--   SZ: pell add two
-- statement:
--   The SZ construction uses the pell add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L72-L72
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean#L72-L72

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
set_option autoImplicit false
open SZ
open Real

theorem SZ.pell_add_two (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := by sorry
