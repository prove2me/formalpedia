-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.actE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:17.781424+00:00
-- url     : https://prove2.me/theorems/b405a4d9-b298-424b-84f4-23900ba5a817
-- title:
--   I2: act E apply
-- statement:
--   The I2 construction uses the act E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L20-L20

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

theorem ReciprocityTheory.ChartRestriction.G.I2.actE_apply (β : E) (v : Vsp dim) (i : Idx dim) : actE β v i = i.1 β * v i := by sorry

attribute [defeq] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
