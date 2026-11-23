-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rk_act_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:01.91218+00:00
-- url     : https://prove2.me/theorems/9e2aef28-2cd1-4b27-8d88-6b7bf6d7acf8
-- title:
--   I2: rk act apply
-- statement:
--   The I2 construction uses the rk act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L16-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
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

theorem ReciprocityTheory.ChartRestriction.G.I2.rk_act_apply (α : 𝓞 E) (v : Vsp dim) (i : Idx dim) : act α v i = i.1 (α : E) * v i := by sorry
