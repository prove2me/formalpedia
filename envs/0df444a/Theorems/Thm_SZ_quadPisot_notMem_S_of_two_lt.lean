-- Prove2me | Theorems.Thm_SZ_quadPisot_notMem_S_of_two_lt
-- name    : SZ.quadPisot_notMem_S_of_two_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:16.150845+00:00
-- url     : https://prove2.me/theorems/bc43856c-e69f-4a80-b56f-dfde27825548
-- title:
--   SZ: quad Pisot not Mem S of two lt
-- statement:
--   **[Dub06EO] Problem 5 loses its whole natural class.**  No quadratic Pisot number
--   greater than `2` lies in `𝒮`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Classification.lean#L142-L150
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Classification.lean#L142-L150

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
set_option autoImplicit false
open SZ
open Real

theorem SZ.quadPisot_notMem_S_of_two_lt {α : ℝ} (h : IsQuadPisot α) (hα : 2 < α) :
    α ∉ S := by sorry
