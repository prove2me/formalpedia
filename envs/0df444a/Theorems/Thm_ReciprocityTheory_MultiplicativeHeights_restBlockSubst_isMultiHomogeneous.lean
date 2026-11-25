-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_restBlockSubst_isMultiHomogeneous
-- name    : ReciprocityTheory.MultiplicativeHeights.restBlockSubst_isMultiHomogeneous
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:44.247422+00:00
-- url     : https://prove2.me/theorems/ebf2282c-27cf-4f8e-9b93-42bb41b23a72
-- title:
--   Multiplicative Heights: rest Block Subst is Multi Homogeneous
-- statement:
--   The Multiplicative Heights construction uses the rest Block Subst is Multi Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L162-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L162-L199

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

theorem ReciprocityTheory.MultiplicativeHeights.restBlockSubst_isMultiHomogeneous {B n : ℕ} {a : Fin (B + 1) → ℕ}
    {g : MvPolynomial (Fin (B + 1) × Fin n) ℂ} (hg : IsMultiHomogeneous a g) (x : Fin n → ℂ) :
    IsMultiHomogeneous (fun b => a b.succ) (aeval (lh0Rest x) g) := by sorry
