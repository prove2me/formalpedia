-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_psiF_rmul
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.psiF_rmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:43.683451+00:00
-- url     : https://prove2.me/theorems/88d8e254-3ba6-5467-81a9-24eb4c51a6ee
-- title:
--   Poin Pf: psi F rmul
-- statement:
--   The Poin Pf construction uses the psi F rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfI.lean#L24-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfI.lean#L24-L44

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.psiF_rmul (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hP : IsBEq X la P) (hW : IsMetricW X la W) :
    ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, psiF X x0 bb P W (rmul y b) = psiF X x0 bb P W y := by sorry
