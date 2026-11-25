-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Hg_lact_cpt
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.KU.Hg_lact_cpt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:53.73002+00:00
-- url     : https://prove2.me/theorems/0d2436c2-7dae-5af4-aa2b-b513647ae52f
-- title:
--   KU: Hg lact cpt
-- statement:
--   The KU construction uses the Hg lact cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPf.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPf.lean#L46-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.KU.Hg_lact_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (FF : Set (V (nd X))) (bb : ℝ)
    {φ : Frame X.Ψ r → ℝ≥0∞} (hφΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Hg X x0 FF bb φ γ (lact γ (cpt X x0 z)) =
      FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ (cpt X x0 z))) * φ (cpt X x0 z)) z := by sorry
