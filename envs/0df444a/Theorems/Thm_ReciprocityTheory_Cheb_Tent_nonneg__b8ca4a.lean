-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_Tent_nonneg__b8ca4a
-- name    : ReciprocityTheory.Cheb.Tent_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:36.987469+00:00
-- url     : https://prove2.me/theorems/b8ca4a94-8567-4cf3-bfb4-d4bee8fc22c7
-- title:
--   Cheb: Tent nonneg
-- statement:
--   The Cheb construction uses the Tent nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L86-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.Cheb.Tent_nonneg (y : ι → ℝ) : 0 ≤ Tent y := by sorry
