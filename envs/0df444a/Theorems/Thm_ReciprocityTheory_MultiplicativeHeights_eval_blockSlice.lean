-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_blockSlice
-- name    : ReciprocityTheory.MultiplicativeHeights.eval_blockSlice
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:00.896432+00:00
-- url     : https://prove2.me/theorems/0d4229bd-c03b-560c-8cfb-3f26db18f57a
-- title:
--   Multiplicative Heights: eval block Slice
-- statement:
--   The Multiplicative Heights construction uses the eval block Slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCores.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCores.lean#L34-L45

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCores
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

theorem ReciprocityTheory.MultiplicativeHeights.eval_blockSlice {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) ℂ) (b : Fin B)
    (p : Fin B → Fin n → ℂ) (w : Fin n → ℂ) :
    eval w (bind₁ (blockSlice b p) f) = eval (fun q => Function.update p b w q.1 q.2) f := by sorry
