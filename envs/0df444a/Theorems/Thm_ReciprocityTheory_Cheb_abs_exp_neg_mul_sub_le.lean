-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_exp_neg_mul_sub_le
-- name    : ReciprocityTheory.Cheb.abs_exp_neg_mul_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:33.891427+00:00
-- url     : https://prove2.me/theorems/3e20cdb1-64ec-5566-8b88-994c029c98d3
-- title:
--   Cheb: abs exp neg mul sub le
-- statement:
--   The Cheb construction uses the abs exp neg mul sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L30-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L30-L56

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.abs_exp_neg_mul_sub_le {s u v L : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hu : L ≤ u) (hv : L ≤ v) :
    |Real.exp (-s * u) - Real.exp (-s * v)| ≤ s * |u - v| * Real.exp (-L) := by sorry
