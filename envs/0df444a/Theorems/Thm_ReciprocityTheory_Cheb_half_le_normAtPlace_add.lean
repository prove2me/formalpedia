-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_half_le_normAtPlace_add
-- name    : ReciprocityTheory.Cheb.half_le_normAtPlace_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:08.450358+00:00
-- url     : https://prove2.me/theorems/09d2b73c-b068-4a93-86bd-6fd5cb6a3e63
-- title:
--   Cheb: half le norm At Place add
-- statement:
--   The Cheb construction uses the half le norm At Place add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L94-L98

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
variable {y k : mixedSpace E} {B a : ℝ}

theorem ReciprocityTheory.Cheb.half_le_normAtPlace_add (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : normAtPlace w y / 2 ≤ normAtPlace w (y + k) := by sorry
