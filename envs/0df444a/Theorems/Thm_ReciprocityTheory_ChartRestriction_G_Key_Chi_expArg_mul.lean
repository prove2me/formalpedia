-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_expArg_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:59.011167+00:00
-- url     : https://prove2.me/theorems/a91aa918-c822-43f3-b6ee-4c5939265dc8
-- title:
--   Chi: exp Arg mul
-- statement:
--   The Chi construction uses the exp Arg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/Blocks.lean#L80-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/Blocks.lean#L80-L99

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg_mul {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (hδ : IsUnit (jAut δ τ).det)
    (hγ : IsUnit (jAut γ (spAct δ τ)).det)
    (hA : (cMat δ).toBlocks₁₁ - spAct δ τ * (cMat δ).toBlocks₂₁ = ((jAut δ τ)⁻¹)ᵀ)
    (z : Fin g → ℂ) :
    expArg (γ * δ) τ z = expArg γ (spAct δ τ) (zAct δ τ z) + expArg δ τ z := by sorry
