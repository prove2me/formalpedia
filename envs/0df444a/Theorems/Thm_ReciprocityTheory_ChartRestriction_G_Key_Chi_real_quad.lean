-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_real_quad
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.real_quad
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:58.278651+00:00
-- url     : https://prove2.me/theorems/f3e4624e-d764-55f5-98e0-393df097be35
-- title:
--   Chi: real quad
-- statement:
--   The Chi construction uses the real quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SubConjTransposeOfSymm.lean#L174-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SubConjTransposeOfSymm.lean#L174-L178

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.real_quad {g : ℕ} (σ : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℝ) :
    ((x ⬝ᵥ (σ.map Complex.im *ᵥ x) : ℝ) : ℂ) =
      star (fun i => (x i : ℂ)) ⬝ᵥ (imC σ *ᵥ fun i => (x i : ℂ)) := by sorry
