-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SpanTopOfComplete_span_eq_top_of_complete
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete.span_eq_top_of_complete
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:30.069431+00:00
-- url     : https://prove2.me/theorems/17e34659-accd-4ce4-9ed6-939ed5c7121e
-- title:
--   Span Top Of Complete: span eq top of complete
-- statement:
--   The Span Top Of Complete construction uses the span eq top of complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SpanTopOfComplete.lean#L5-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SpanTopOfComplete.lean#L5-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpanTopOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete

theorem ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete.span_eq_top_of_complete {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N] (ϖ : O)
    [IsPrecomplete (Ideal.span {ϖ}) O]
    (hsep : ∀ x : N, (∀ k : ℕ, ∃ y : N, x = ϖ ^ k • y) → x = 0) {n : ℕ} (S : Fin n → N)
    (hS : ∀ x : N, ∃ c : Fin n → O, ∃ y : N, x = ∑ i, c i • S i + ϖ • y) :
    Submodule.span O (Set.range S) = ⊤ := by sorry
