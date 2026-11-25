-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_cunfold_one
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cunfold_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:38.859495+00:00
-- url     : https://prove2.me/theorems/4b3e0043-c949-596a-845b-71575bebb9b5
-- title:
--   Pair Unfold Pf: cunfold one
-- statement:
--   The Pair Unfold Pf construction uses the cunfold one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfB.lean#L635-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfB.lean#L635-L670

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cunfold_one (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (G : Frame X.Ψ r → ℂ) (hG : Measurable G)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∫ z in FF, G (lact γ (cpt X x0 z)) ∂muF X x0 =
      ∫ z, (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ⁻¹ (cpt X x0 z)) * G (cpt X x0 z) ∂muF X x0 := by sorry
