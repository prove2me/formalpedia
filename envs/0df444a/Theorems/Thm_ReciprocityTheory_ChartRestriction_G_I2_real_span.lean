-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_real_span
-- name    : ReciprocityTheory.ChartRestriction.G.I2.real_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:12.315352+00:00
-- url     : https://prove2.me/theorems/7ab176e5-066e-4080-94fc-022d426f1968
-- title:
--   I2: real span
-- statement:
--   The I2 construction uses the real span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L75-L86

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

theorem ReciprocityTheory.ChartRestriction.G.I2.real_span (t : (E →+* ℂ) → ℂ) (ht : ConjSymm t) :
    ∃ c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      t = ∑ k, c k • canonicalEmbedding E (integralBasis E k) := by sorry
