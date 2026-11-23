-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_actE__3dabe342590f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_actE__3dabe342590f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:36.71065+00:00
-- url     : https://prove2.me/theorems/b977c053-b190-4eb5-befd-e11a60966d0c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Hf act E  3dabe342590f: P2 M Reciprocity Theory Chart Restriction G I2 Hf act E  3dabe342590f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Hf act E  3dabe342590f construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Hf act E  3dabe342590f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L110-L115

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
variable [IsCMField E]

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_actE__3dabe342590f (β : E) (v w : Vsp dim) :
    Hf v (actE β w) = Hf (actE (IsCMField.complexConj E β) v) w := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«Hf_actE'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_actE__3dabe342590f
