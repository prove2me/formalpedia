-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rkQP_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rkQP_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:14.273125+00:00
-- url     : https://prove2.me/theorems/b6ea50ab-822d-513d-91dd-ba767016de4a
-- title:
--   I2: rk QP apply
-- statement:
--   The I2 construction uses the rk QP apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L77-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L77-L93

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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.rkQP_apply (τ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    rkQ τ (rkP τ v) i = if i.1 = τ then v i else 0 := by sorry
