-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_trT_tmul
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.trT_tmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:46.843224+00:00
-- url     : https://prove2.me/theorems/a018cc0b-277f-4665-bb70-9fbfa1408772
-- title:
--   Desc Pf: tr T tmul
-- statement:
--   The Desc Pf construction uses the tr T tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L15-L17

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.trT_tmul [FiniteDimensional K K₂] (x : K₂) (v : V) :
    trT (x ⊗ₜ[K] v) = Algebra.trace K K₂ x • v := by sorry
