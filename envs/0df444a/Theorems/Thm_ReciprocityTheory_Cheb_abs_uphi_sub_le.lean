-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_uphi_sub_le
-- name    : ReciprocityTheory.Cheb.abs_uphi_sub_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:45.158239+00:00
-- url     : https://prove2.me/theorems/f4b29cf4-4cb6-512f-a7ff-c2bb1e16c82b
-- title:
--   Cheb: abs uphi sub le
-- statement:
--   The Cheb construction uses the abs uphi sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L199-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L199-L203

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
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.abs_uphi_sub_le {x y : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0)
    (hy : mixedEmbedding.norm y ≠ 0) : |uphi x - uphi y| ≤ ∑ i, |ucoord x i - ucoord y i| := by sorry
