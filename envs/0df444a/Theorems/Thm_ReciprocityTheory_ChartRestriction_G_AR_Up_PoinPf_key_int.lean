-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_key_int
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.key_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:36.289056+00:00
-- url     : https://prove2.me/theorems/88a63eb8-9fb1-4bae-9125-4ff5bb1b0798
-- title:
--   Poin Pf: key int
-- statement:
--   The Poin Pf construction uses the key int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfC.lean#L220-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfC.lean#L220-L279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.key_int (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (hW : IsMetricW X la W)
    {c : ℝ} (hc : 0 < c) (hcW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x)
    (P : Frame X.Ψ r → ℂ) (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r} {ρ : ℝ}
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hI : ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)) ≠ ⊤) :
    ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) ≤
      supR X la W ρ x ^ 2 * ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)) := by sorry
