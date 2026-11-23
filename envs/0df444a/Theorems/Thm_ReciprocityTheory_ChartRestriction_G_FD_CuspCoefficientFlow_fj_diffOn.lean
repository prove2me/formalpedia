-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_fj_diffOn
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:50.683486+00:00
-- url     : https://prove2.me/theorems/69969fa3-2107-4f8d-b559-f0d889168fc0
-- title:
--   Cusp Coefficient Flow: fj diff On
-- statement:
--   The Cusp Coefficient Flow construction uses the fj diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L227-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L227-L246

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) : DifferentiableOn ℂ (X.fj la ξ ν P) X.dom := by sorry
