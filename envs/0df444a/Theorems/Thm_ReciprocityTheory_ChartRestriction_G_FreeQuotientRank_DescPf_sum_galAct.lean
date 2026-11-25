-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_sum_galAct
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.sum_galAct
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:33.138475+00:00
-- url     : https://prove2.me/theorems/64503133-2892-4435-8842-16a7988a4a07
-- title:
--   Desc Pf: sum gal Act
-- statement:
--   The Desc Pf construction uses the sum gal Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L23-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.sum_galAct [FiniteDimensional K K₂] [IsGalois K K₂] (y : K₂ ⊗[K] V) :
    ∑ σ : K₂ ≃ₐ[K] K₂, galAct σ y = (1 : K₂) ⊗ₜ[K] trT y := by sorry
