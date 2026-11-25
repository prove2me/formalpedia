-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalLengthAverage_algebraMap_mem_Rv
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage.algebraMap_mem_Rv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:17.559309+00:00
-- url     : https://prove2.me/theorems/c50a3cf7-af6b-5496-9e1d-8cbbc858088c
-- title:
--   Local Length Average: algebra Map mem Rv
-- statement:
--   The Local Length Average construction uses the algebra Map mem Rv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalLengthAverage.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalLengthAverage.lean#L14-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
  ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage.algebraMap_mem_Rv (w : HeightOneSpectrum (𝓞 K₁)) (a : 𝓞 K) :
    algebraMap K K₁ (algebraMap (𝓞 K) K a) ∈ Rv K₁ w := by sorry
