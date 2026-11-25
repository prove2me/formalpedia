-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_so_prod_norm
-- name    : ReciprocityTheory.ChartRestriction.G.I2.so_prod_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:55.687461+00:00
-- url     : https://prove2.me/theorems/160ff5d1-6593-4ede-aa89-185ae5f5389d
-- title:
--   I2: so prod norm
-- statement:
--   The I2 construction uses the so prod norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitOA.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitOA.lean#L11-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.so_prod_norm (x : E) : ∏ σ : E →+* ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by sorry
