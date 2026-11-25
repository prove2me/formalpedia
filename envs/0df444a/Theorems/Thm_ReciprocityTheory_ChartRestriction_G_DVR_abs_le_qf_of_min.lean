-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_abs_le_qf_of_min
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.abs_le_qf_of_min
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:29.906231+00:00
-- url     : https://prove2.me/theorems/c8612f89-1203-418e-9478-528c7e46b779
-- title:
--   DVR: abs le qf of min
-- statement:
--   The DVR construction uses the abs le qf of min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean#L17-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]
variable {B : LinearMap.BilinForm 𝕜 W}

theorem ReciprocityTheory.ChartRestriction.G.DVR.abs_le_qf_of_min (hB : ∀ x y, B x y = B y x) {x μ : W} (h₁ : qf B x ≤ qf B (x + μ))
    (h₂ : qf B x ≤ qf B (x - μ)) : |B x μ| ≤ qf B μ := by sorry
