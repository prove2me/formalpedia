-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_act_mul__84e45c71f726
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_act_mul__84e45c71f726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:27.0911+00:00
-- url     : https://prove2.me/theorems/cd7526cb-1803-43cd-b280-39c62f2fa122
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 act mul  84e45c71f726: P2 M Reciprocity Theory Chart Restriction G I2 act mul  84e45c71f726
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 act mul  84e45c71f726 construction uses the P2 M Reciprocity Theory Chart Restriction G I2 act mul  84e45c71f726 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L66-L69

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_act_mul__84e45c71f726 (α β : 𝓞 E) (v : Vsp dim) : act (α * β) v = act α (act β v) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«act_mul'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_act_mul__84e45c71f726
