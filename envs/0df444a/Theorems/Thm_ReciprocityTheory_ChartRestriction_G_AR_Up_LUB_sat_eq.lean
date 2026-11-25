-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_sat_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.sat_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:37.366671+00:00
-- url     : https://prove2.me/theorems/a68f27bc-c278-591d-8790-5057b6df3644
-- title:
--   LUB: sat eq
-- statement:
--   The LUB construction uses the sat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfC.lean#L115-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfC.lean#L115-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
variable {X b1}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.sat_eq (x1 : Frame X.Ψ r) (ρ : ℝ) :
    {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)} =
      ⋃ γ : X.Γ, lact γ.1⁻¹ ⁻¹' Tset X x1 ρ := by sorry
