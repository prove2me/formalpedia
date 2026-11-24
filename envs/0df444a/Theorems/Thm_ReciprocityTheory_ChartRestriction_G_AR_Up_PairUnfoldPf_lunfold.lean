-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_lunfold
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lunfold
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:41.546846+00:00
-- url     : https://prove2.me/theorems/cd8252f3-1a04-4b21-b3a0-753b7c5b7946
-- title:
--   Pair Unfold Pf: lunfold
-- statement:
--   The Pair Unfold Pf construction uses the lunfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfB.lean#L531-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfB.lean#L531-L566

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
include D

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lunfold (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∑' γ : X.Γ, ∫⁻ z in FF, φ (lact γ.1 (cpt X x0 z)) ∂muF X x0 = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 := by sorry
