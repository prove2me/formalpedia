-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_conjugate_ne
-- name    : ReciprocityTheory.ChartRestriction.G.I2.conjugate_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:42.381014+00:00
-- url     : https://prove2.me/theorems/ea852a37-bba4-42fe-8f42-be89f163273e
-- title:
--   I2: conjugate ne
-- statement:
--   The I2 construction uses the conjugate ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L88-L92

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

theorem ReciprocityTheory.ChartRestriction.G.I2.conjugate_ne [IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by sorry
