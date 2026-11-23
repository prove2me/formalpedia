-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_fj_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.fj_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:43.635147+00:00
-- url     : https://prove2.me/theorems/97e26e98-82ac-4e9a-bc97-1f98558f5a8d
-- title:
--   Flow Coefficient Bounds: fj bound
-- statement:
--   The Flow Coefficient Bounds construction uses the fj bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientBounds.lean#L118-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientBounds.lean#L118-L143

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.fj_bound (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C : ℝ)
    (hP : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la (X.fj la ξ ν P) x ≤ C := by sorry
