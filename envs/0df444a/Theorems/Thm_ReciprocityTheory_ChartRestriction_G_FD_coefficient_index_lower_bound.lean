-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_coefficient_index_lower_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.coefficient_index_lower_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:57.121498+00:00
-- url     : https://prove2.me/theorems/ab839b8f-bbbf-5a8d-94f5-853d659e9198
-- title:
--   FD: coefficient index lower bound
-- statement:
--   The FD construction uses the coefficient index lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientIndexLowerBound.lean#L86-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientIndexLowerBound.lean#L86-L244

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientIndexLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.coefficient_index_lower_bound (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientIndexLowerBound (E := E) := by sorry
