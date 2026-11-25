-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_galAct_tmul
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.galAct_tmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:06.965128+00:00
-- url     : https://prove2.me/theorems/c5e8786d-5194-482d-b194-11285fa41f3f
-- title:
--   Desc Pf: gal Act tmul
-- statement:
--   The Desc Pf construction uses the gal Act tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L19-L21

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.galAct_tmul (σ : K₂ ≃ₐ[K] K₂) (x : K₂) (v : V) :
    galAct σ (x ⊗ₜ[K] v) = σ x ⊗ₜ[K] v := by sorry
