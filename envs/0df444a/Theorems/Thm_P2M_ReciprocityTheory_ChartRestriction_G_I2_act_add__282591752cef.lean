-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_act_add__282591752cef
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_act_add__282591752cef
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:12.380826+00:00
-- url     : https://prove2.me/theorems/2722a121-8fff-42c7-8dc8-210c48b5fcae
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 act add  282591752cef: P2 M Reciprocity Theory Chart Restriction G I2 act add  282591752cef
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 act add  282591752cef construction uses the P2 M Reciprocity Theory Chart Restriction G I2 act add  282591752cef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsMaximal.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsMaximal.lean#L12-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_act_add__282591752cef {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«act_add'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_act_add__282591752cef
