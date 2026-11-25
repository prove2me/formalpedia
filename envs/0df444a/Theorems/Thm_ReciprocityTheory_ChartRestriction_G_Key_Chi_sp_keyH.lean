-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_keyH
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_keyH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:17.189802+00:00
-- url     : https://prove2.me/theorems/b4b34732-23a9-448e-9199-785c4e56b4ad
-- title:
--   Chi: sp key H
-- statement:
--   The Chi construction uses the sp key H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SubConjTransposeOfSymm.lean#L73-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SubConjTransposeOfSymm.lean#L73-L107

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_keyH {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (jAut γ τ)ᴴ * nAut γ τ - (nAut γ τ)ᴴ * jAut γ τ = τ - τᴴ := by sorry
