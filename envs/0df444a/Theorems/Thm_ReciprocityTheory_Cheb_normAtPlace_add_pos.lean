-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_normAtPlace_add_pos
-- name    : ReciprocityTheory.Cheb.normAtPlace_add_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:12.709129+00:00
-- url     : https://prove2.me/theorems/4abc4ede-c451-4014-9ecf-db6b1b11784d
-- title:
--   Cheb: norm At Place add pos
-- statement:
--   The Cheb construction uses the norm At Place add pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L100-L103

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

theorem ReciprocityTheory.Cheb.normAtPlace_add_pos (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : 0 < normAtPlace w (y + k) := by sorry
