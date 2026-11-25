-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_continuousAt_nfac
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.continuousAt_nfac
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:03.229053+00:00
-- url     : https://prove2.me/theorems/9419c98a-626e-4dd2-a693-39553e0ab8d6
-- title:
--   Cusp Coefficient Flow: continuous At nfac
-- statement:
--   The Cusp Coefficient Flow construction uses the continuous At nfac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L171-L182

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.continuousAt_nfac (la : Wt X.Ψ r) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ContinuousAt (X.nfac la) x0 := by sorry
