-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_conjSymm_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.conjSymm_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:48.700494+00:00
-- url     : https://prove2.me/theorems/a88626c8-8377-44b8-8621-7cc512a3359a
-- title:
--   I2: conj Symm sum
-- statement:
--   The I2 construction uses the conj Symm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L43-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.conjSymm_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (v : ι → (E →+* ℂ) → ℂ)
    (hv : ∀ i, ConjSymm (v i)) : ConjSymm (∑ i ∈ s, c i • v i) := by sorry
