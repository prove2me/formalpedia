-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_isOrth_lact
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.isOrth_lact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:05.96181+00:00
-- url     : https://prove2.me/theorems/2a25d89e-402d-49c5-ac3a-abd19b286121
-- title:
--   Pair Unfold Pf: is Orth lact
-- statement:
--   The Pair Unfold Pf construction uses the is Orth lact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfA.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfA.lean#L98-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.isOrth_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x0 : Frame X.Ψ r} (h : IsOrth X x0) :
    IsOrth X (lact γ x0) := by sorry
