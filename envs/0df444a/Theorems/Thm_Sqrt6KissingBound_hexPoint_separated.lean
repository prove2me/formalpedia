-- Prove2me | Theorems.Thm_Sqrt6KissingBound_hexPoint_separated
-- name    : Sqrt6KissingBound.hexPoint_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:11:42.579751+00:00
-- url     : https://prove2.me/theorems/a27f6979-6fb2-4614-bb40-5bcd858a29ff
-- title:
--   Sqrt6 Kissing Bound: hex Point separated
-- statement:
--   The Sqrt6 Kissing Bound construction uses the hex Point separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L49-L53
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L49-L53

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.hexPoint_separated (i j : Fin 6) (hij : i ≠ j) :
    inner ℝ (hexPoint i) (hexPoint j) ≤ (1 : ℝ) / 2 := by sorry
