-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_C_mul
-- name    : ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_C_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:22.625004+00:00
-- url     : https://prove2.me/theorems/21e8533f-da79-574e-9d7e-6f857c208451
-- title:
--   Multiplicative Heights: is Multi Homogeneous C mul
-- statement:
--   The Multiplicative Heights construction uses the is Multi Homogeneous C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L39-L43

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

theorem ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_C_mul {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) : IsMultiHomogeneous a (C c * g) := by sorry
