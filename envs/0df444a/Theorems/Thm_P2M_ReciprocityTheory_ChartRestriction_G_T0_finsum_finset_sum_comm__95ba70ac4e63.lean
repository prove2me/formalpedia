-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_finsum_finset_sum_comm__95ba70ac4e63
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_finsum_finset_sum_comm__95ba70ac4e63
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:05:13.073536+00:00
-- url     : https://prove2.me/theorems/c35a06f3-90b1-45a8-88dd-532cfbeb7c4c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 finsum finset sum comm  95ba70ac4e63: P2 M Reciprocity Theory Chart Restriction G T0 finsum finset sum comm  95ba70ac4e63
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 finsum finset sum comm  95ba70ac4e63 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 finsum finset sum comm  95ba70ac4e63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightDecompositionLocalTerms.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightDecompositionLocalTerms.lean#L7-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteLocalHeightTerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightDecompositionLocalTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_finsum_finset_sum_comm__95ba70ac4e63 {α β : Type*} (s : Finset β) (f : β → α → ℝ)
    (hf : ∀ b ∈ s, (Function.support (f b)).Finite) :
    ∑ᶠ a, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑ᶠ a, f b a := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«finsum_finset_sum_comm'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_finsum_finset_sum_comm__95ba70ac4e63
