-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trace_gram_det_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.trace_gram_det_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:25.677606+00:00
-- url     : https://prove2.me/theorems/1679c1fb-19b5-58f3-9ce4-bd31acf73d3f
-- title:
--   T0: trace gram det ne zero
-- statement:
--   The T0 construction uses the trace gram det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TraceGramDetNeZero.lean#L8-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TraceGramDetNeZero.lean#L8-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TraceGramDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.trace_gram_det_ne_zero {F : Type} [Field F] [CharZero F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {E : κ → Type} [∀ c, Field (E c)] [∀ c, Algebra F (E c)] [∀ c, FiniteDimensional F (E c)]
    {n : ℕ} (b : Fin n → ∀ c, E c)
    (hind : ∀ v : Fin n → F, (∀ c, ∑ l, v l • b l c = 0) → v = 0)
    (hspan : ∀ y : ∀ c, E c, ∃ μ : Fin n → F, ∀ c, y c = ∑ k, μ k • b k c) :
    (Matrix.of fun k l : Fin n => ∑ c, Algebra.trace F (E c) (b k c * b l c)).det ≠ 0 := by sorry
