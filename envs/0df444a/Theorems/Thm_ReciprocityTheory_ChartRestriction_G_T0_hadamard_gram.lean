-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hadamard_gram
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hadamard_gram
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:41.088745+00:00
-- url     : https://prove2.me/theorems/54d1eeab-b17a-456d-aecd-cdac5db409b8
-- title:
--   T0: hadamard gram
-- statement:
--   The T0 construction uses the hadamard gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HadamardGram.lean#L8-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HadamardGram.lean#L8-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HadamardGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix

theorem ReciprocityTheory.ChartRestriction.G.T0.hadamard_gram {R : Type*} [Fintype R] [DecidableEq R] {n : ℕ} (hR : Fintype.card R = n)
    (M : R → Fin n → ℂ) (ν : R → ℝ) (s : Fin n → ℝ) (hν : ∀ r, 0 < ν r)
    (hM : ∀ r k, ‖M r k‖ * ν r ≤ s k) :
    ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2 ≤
      (n : ℝ) ^ n * ∏ k, s k ^ 2 := by sorry
