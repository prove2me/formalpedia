-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_dot_conj
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.dot_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:24.119163+00:00
-- url     : https://prove2.me/theorems/663af9c3-6a89-50c5-8940-35e5a454b942
-- title:
--   Chi: dot conj
-- statement:
--   The Chi construction uses the dot conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/Blocks.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/Blocks.lean#L75-L78

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.dot_conj {g : ℕ} (P Y : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    z ⬝ᵥ ((P * Y * Pᵀ) *ᵥ z) = (Pᵀ *ᵥ z) ⬝ᵥ (Y *ᵥ (Pᵀ *ᵥ z)) := by sorry
