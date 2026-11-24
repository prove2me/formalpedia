-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_rel
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:35.142334+00:00
-- url     : https://prove2.me/theorems/b3a2e4d6-efcb-4196-87d5-8305fa98906b
-- title:
--   Chi: sp rel
-- statement:
--   The Chi construction uses the sp rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/Blocks.lean#L101-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/Blocks.lean#L101-L124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_rel {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₂₁ᵀ * (cMat γ).toBlocks₁₁ - (cMat γ).toBlocks₁₁ᵀ * (cMat γ).toBlocks₂₁ = 0) ∧
    ((cMat γ).toBlocks₂₁ᵀ * (cMat γ).toBlocks₁₂ - (cMat γ).toBlocks₁₁ᵀ * (cMat γ).toBlocks₂₂ = -1) ∧
    ((cMat γ).toBlocks₂₂ᵀ * (cMat γ).toBlocks₁₁ - (cMat γ).toBlocks₁₂ᵀ * (cMat γ).toBlocks₂₁ = 1) ∧
    ((cMat γ).toBlocks₂₂ᵀ * (cMat γ).toBlocks₁₂ - (cMat γ).toBlocks₁₂ᵀ * (cMat γ).toBlocks₂₂ = 0) := by sorry
