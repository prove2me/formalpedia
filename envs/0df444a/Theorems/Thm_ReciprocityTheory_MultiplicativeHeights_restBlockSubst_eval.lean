-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_restBlockSubst_eval
-- name    : ReciprocityTheory.MultiplicativeHeights.restBlockSubst_eval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:32.956052+00:00
-- url     : https://prove2.me/theorems/8e3ca907-c63a-428a-86df-c921f8550165
-- title:
--   Multiplicative Heights: rest Block Subst eval
-- statement:
--   The Multiplicative Heights construction uses the rest Block Subst eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L119-L125

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

theorem ReciprocityTheory.MultiplicativeHeights.restBlockSubst_eval {B n : ℕ} (x : UnitSphereC n) (y : BlockSphere B n) :
    (fun p => eval (blockPoint y) (lh0Rest (spherePoint x) p)) =
      blockPoint ((lh0Split B n).symm (x, y)) := by sorry
