-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_tmul__4dfde58e6361
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_tmul__4dfde58e6361
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:46.509846+00:00
-- url     : https://prove2.me/theorems/82876fab-f59d-4e7b-8f69-8cdd641fcca3
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Free Quotient Rank incl T tmul  4dfde58e6361: P2 M Reciprocity Theory Chart Restriction G Free Quotient Rank incl T tmul  4dfde58e6361
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Free Quotient Rank incl T tmul  4dfde58e6361 construction uses the P2 M Reciprocity Theory Chart Restriction G Free Quotient Rank incl T tmul  4dfde58e6361 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L53-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
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
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem P2M_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_tmul__4dfde58e6361 (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) ⊗ₜ[K] v := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FreeQuotientRank».«inclT_tmul'» := P2M_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_tmul__4dfde58e6361
