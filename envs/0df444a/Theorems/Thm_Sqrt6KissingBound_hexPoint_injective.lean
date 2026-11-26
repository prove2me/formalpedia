-- Prove2me | Theorems.Thm_Sqrt6KissingBound_hexPoint_injective
-- name    : Sqrt6KissingBound.hexPoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:17:35.386874+00:00
-- url     : https://prove2.me/theorems/387b2bdd-67af-5bdb-8cf9-b35dad2d5339
-- title:
--   Sqrt6 Kissing Bound: hex Point injective
-- statement:
--   The Sqrt6 Kissing Bound construction uses the hex Point injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L55-L62
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean#L55-L62

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.hexPoint_injective : Function.Injective hexPoint := by sorry
