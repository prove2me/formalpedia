-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.I2.actE_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:22.472774+00:00
-- url     : https://prove2.me/theorems/813bfb1a-4081-4ded-bcf7-f354231aa423
-- title:
--   I2: act E smul right
-- statement:
--   The I2 construction uses the act E smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L26-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.actE_smul_right (β : E) (c : ℂ) (v : Vsp dim) : actE β (c • v) = c • actE β v := by sorry
