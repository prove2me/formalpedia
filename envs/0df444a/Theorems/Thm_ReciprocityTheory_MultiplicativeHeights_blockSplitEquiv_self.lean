-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSplitEquiv_self
-- name    : ReciprocityTheory.MultiplicativeHeights.blockSplitEquiv_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:43.535069+00:00
-- url     : https://prove2.me/theorems/04f8f375-3d33-4c32-bc74-0293219498e1
-- title:
--   Multiplicative Heights: block Split Equiv self
-- statement:
--   The Multiplicative Heights construction uses the block Split Equiv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L127-L131

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.blockSplitEquiv_self {B n : ℕ} (u : BlockSphere (B + 1) n) :
    (lh0Split B n).symm (u 0, fun b => u b.succ) = u := by sorry
