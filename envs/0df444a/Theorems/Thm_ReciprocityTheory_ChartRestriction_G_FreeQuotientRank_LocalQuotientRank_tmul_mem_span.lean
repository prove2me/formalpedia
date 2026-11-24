-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_tmul_mem_span
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.tmul_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:38:45.914926+00:00
-- url     : https://prove2.me/theorems/73f05d67-e72f-436f-893b-954afeb552f3
-- title:
--   Local Quotient Rank: tmul mem span
-- statement:
--   The Local Quotient Rank construction uses the tmul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalQuotientRank.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalQuotientRank.lean#L76-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
open NumberField Module
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.tmul_mem_span {ι : Type*} (g : ι → V) {y : V} (hy : y ∈ Submodule.span K (Set.range g)) :
    (1 : K₁) ⊗ₜ[K] y ∈ Submodule.span K₁ (Set.range fun j => (1 : K₁) ⊗ₜ[K] g j) := by sorry
