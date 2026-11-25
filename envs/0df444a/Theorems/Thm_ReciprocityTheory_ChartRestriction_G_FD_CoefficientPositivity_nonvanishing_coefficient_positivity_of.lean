-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_nonvanishing_coefficient_positivity_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.nonvanishing_coefficient_positivity_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:37.403798+00:00
-- url     : https://prove2.me/theorems/5b502890-5400-5e55-b063-0bc9791bd598
-- title:
--   Coefficient Positivity: nonvanishing coefficient positivity of
-- statement:
--   The Coefficient Positivity construction uses the nonvanishing coefficient positivity of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L253-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L253-L333

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.nonvanishing_coefficient_positivity_of (h2 : UnipotentLatticeLift (E := E)) (h3 : FourierCoefficientProperties (E := E)) :
    NonvanishingCoefficientPositivity (E := E) := by sorry
