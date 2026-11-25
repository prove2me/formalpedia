-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___0ce1162e1798
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___0ce1162e1798
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:19.135725+00:00
-- url     : https://prove2.me/theorems/7f6a268c-a05a-4377-9bc3-58a9cf6acfc6
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Key Chi blk conj Transpose   0ce1162e1798: P2 M Reciprocity Theory Chart Restriction G Key Chi blk conj Transpose   0ce1162e1798
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Key Chi blk conj Transpose   0ce1162e1798 construction uses the P2 M Reciprocity Theory Chart Restriction G Key Chi blk conj Transpose   0ce1162e1798 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SubConjTransposeOfSymm.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SubConjTransposeOfSymm.lean#L63-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___0ce1162e1798 {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ((cMat γ).toBlocks₁₁)ᴴ = ((cMat γ).toBlocks₁₁)ᵀ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Key».«Chi».«blk_conjTranspose₁₁» := P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___0ce1162e1798
