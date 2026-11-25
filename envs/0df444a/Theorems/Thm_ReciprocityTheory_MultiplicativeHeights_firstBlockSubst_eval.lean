-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_firstBlockSubst_eval
-- name    : ReciprocityTheory.MultiplicativeHeights.firstBlockSubst_eval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:23.41296+00:00
-- url     : https://prove2.me/theorems/e831c814-773a-5f43-9358-396c57328d51
-- title:
--   Multiplicative Heights: first Block Subst eval
-- statement:
--   The Multiplicative Heights construction uses the first Block Subst eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L111-L117

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

theorem ReciprocityTheory.MultiplicativeHeights.firstBlockSubst_eval {B n : ℕ} (x : UnitSphereC n) (y : BlockSphere B n) :
    (fun p => eval (spherePoint x) (lh0First y p)) =
      blockPoint ((lh0Split B n).symm (x, y)) := by sorry
