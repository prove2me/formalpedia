-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_norm_cexp_I
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.norm_cexp_I
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:55.148595+00:00
-- url     : https://prove2.me/theorems/7935bfba-9928-4763-b035-c9d60b9551b3
-- title:
--   Flow Coefficient Bounds: norm cexp I
-- statement:
--   The Flow Coefficient Bounds construction uses the norm cexp I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientBounds.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientBounds.lean#L25-L27

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.norm_cexp_I (z : ℂ) (hz : z.im = 0) : ‖cexp (-(4 * (Real.pi : ℂ) * I) * z)‖ = 1 := by sorry
