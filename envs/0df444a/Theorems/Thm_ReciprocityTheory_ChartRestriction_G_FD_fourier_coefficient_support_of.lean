-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_fourier_coefficient_support_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.fourier_coefficient_support_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:11.416979+00:00
-- url     : https://prove2.me/theorems/0f46c3d8-89f8-5e2c-bda3-172214b92333
-- title:
--   FD: fourier coefficient support of
-- statement:
--   The FD construction uses the fourier coefficient support of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientSupportHolds.lean#L23-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientSupportHolds.lean#L23-L244

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentLatticeLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.fourier_coefficient_support_of (h3 : FourierCoefficientProperties (E := E)) (h2 : UnipotentLatticeLift (E := E)) :
    FourierCoefficientSupport (E := E) := by sorry
