-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_coefficient_height_bound_of_lift_support_positivity
-- name    : ReciprocityTheory.ChartRestriction.G.FD.coefficient_height_bound_of_lift_support_positivity
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:04.432797+00:00
-- url     : https://prove2.me/theorems/4e93ab79-36f7-530c-a7f1-9b62618348a0
-- title:
--   FD: coefficient height bound of lift support positivity
-- statement:
--   The FD construction uses the coefficient height bound of lift support positivity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientHeightBoundOfLiftSupportPositivity.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientHeightBoundOfLiftSupportPositivity.lean#L260-L262

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticOffDiagonalBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientHeightBoundOfLiftSupportPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.coefficient_height_bound_of_lift_support_positivity (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientHeightBound (E := E) := by sorry
