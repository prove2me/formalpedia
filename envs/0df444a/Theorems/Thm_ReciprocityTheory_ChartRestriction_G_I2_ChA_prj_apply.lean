-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_prj_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ChA.prj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:47.891607+00:00
-- url     : https://prove2.me/theorems/923871dc-e54c-4cf6-a9eb-0a0f3ec0a78a
-- title:
--   Ch A: prj apply
-- statement:
--   The Ch A construction uses the prj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L39-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
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
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.ChA.prj_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    prj σ v i = if i.1 = σ then v i else 0 := by sorry
