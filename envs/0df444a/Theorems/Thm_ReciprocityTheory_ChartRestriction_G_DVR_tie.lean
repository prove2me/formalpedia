-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tie
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.tie
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:50.494074+00:00
-- url     : https://prove2.me/theorems/7f4ed606-627c-4deb-bc55-9715c1142f3b
-- title:
--   DVR: tie
-- statement:
--   The DVR construction uses the tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/QuadTie.lean#L23-L28

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.tie (hB : ∀ x y, B x y = B y x) {x μ : W} (h₁ : qf B x ≤ qf B (x + μ)) (h₂ : qf B x ≤ qf B (x - μ))
    (k : ℕ) : (k : 𝕜) * ((k : 𝕜) - 1) * qf B μ ≤ qf B (x + (k : 𝕜) • μ) - qf B x := by sorry
