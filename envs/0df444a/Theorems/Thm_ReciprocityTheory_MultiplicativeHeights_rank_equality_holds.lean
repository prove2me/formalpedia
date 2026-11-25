-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_rank_equality_holds
-- name    : ReciprocityTheory.MultiplicativeHeights.rank_equality_holds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:52.356009+00:00
-- url     : https://prove2.me/theorems/b9cc32e1-3d7c-4225-a214-b74bb0b86a6d
-- title:
--   Multiplicative Heights: rank equality holds
-- statement:
--   The Multiplicative Heights construction uses the rank equality holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RankEqualityHolds.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RankEqualityHolds.lean#L8-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_RankEqualityHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct

theorem ReciprocityTheory.MultiplicativeHeights.rank_equality_holds : RankStatement := by sorry
