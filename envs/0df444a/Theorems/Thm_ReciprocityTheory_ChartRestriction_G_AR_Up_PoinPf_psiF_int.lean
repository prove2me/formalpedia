-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_psiF_int
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.psiF_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:51.338867+00:00
-- url     : https://prove2.me/theorems/2bfbad68-0397-54a9-abee-d1260c22930d
-- title:
--   Poin Pf: psi F int
-- statement:
--   The Poin Pf construction uses the psi F int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfI.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfI.lean#L53-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.psiF_int (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) {P : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞} {F : V (nd X) → ℂ} (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) :
    ∫⁻ z, psiF X x0 bb P W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 := by sorry
