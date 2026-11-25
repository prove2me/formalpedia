-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_nonvanishing_coefficient_positivity
-- name    : ReciprocityTheory.ChartRestriction.G.FD.nonvanishing_coefficient_positivity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:50:43.019824+00:00
-- url     : https://prove2.me/theorems/a3676333-23af-4f1b-9310-1238373474a9
-- title:
--   FD: nonvanishing coefficient positivity
-- statement:
--   The FD construction uses the nonvanishing coefficient positivity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NonvanishingCoefficientPositivity.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NonvanishingCoefficientPositivity.lean#L10-L10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentLatticeLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingCoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.nonvanishing_coefficient_positivity : NonvanishingCoefficientPositivity (E := E) := by sorry
