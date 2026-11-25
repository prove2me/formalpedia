-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_firstBlockSubst_isHomogeneous
-- name    : ReciprocityTheory.MultiplicativeHeights.firstBlockSubst_isHomogeneous
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:50.006427+00:00
-- url     : https://prove2.me/theorems/7e869aa6-4a63-5f85-8774-33a395c0174b
-- title:
--   Multiplicative Heights: first Block Subst is Homogeneous
-- statement:
--   The Multiplicative Heights construction uses the first Block Subst is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L145-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L145-L160

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

theorem ReciprocityTheory.MultiplicativeHeights.firstBlockSubst_isHomogeneous {B n : ℕ} {a : Fin (B + 1) → ℕ}
    {g : MvPolynomial (Fin (B + 1) × Fin n) ℂ} (hg : IsMultiHomogeneous a g)
    (y : BlockSphere B n) : (aeval (lh0First y) g).IsHomogeneous (a 0) := by sorry
