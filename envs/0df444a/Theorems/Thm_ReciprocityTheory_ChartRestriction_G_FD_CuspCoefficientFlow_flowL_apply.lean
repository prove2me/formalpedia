-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_flowL_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.flowL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:34.569792+00:00
-- url     : https://prove2.me/theorems/b7740ca5-e738-4822-9df8-133d6a8a6c13
-- title:
--   Cusp Coefficient Flow: flow L apply
-- statement:
--   The Cusp Coefficient Flow construction uses the flow L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L146-L147

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.flowL_apply (ξ : Fin r → E) (s : X.Ψ → ℝ) (x : Frame X.Ψ r) :
    flowL X ξ s x = X.flow ξ (fun τ => (s τ : ℂ)) x := by sorry
