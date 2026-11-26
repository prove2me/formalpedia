-- Prove2me | Theorems.Thm_Sqrt6KissingBound_hexPoint_norm
-- name    : Sqrt6KissingBound.hexPoint_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:10:38.437019+00:00
-- url     : https://prove2.me/theorems/9f7086c6-49e7-4684-81b7-5d8e7ace8f19
-- title:
--   Sqrt6 Kissing Bound: hex Point norm
-- statement:
--   The Sqrt6 Kissing Bound construction uses the hex Point norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L46-L47
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L46-L47

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.hexPoint_norm (i : Fin 6) : ‖hexPoint i‖ = 1 := by sorry
