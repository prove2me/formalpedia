-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_one_eq_spTransl_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.one_eq_spTransl_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:44.061733+00:00
-- url     : https://prove2.me/theorems/f9ff264c-ec0f-5261-aa64-a9ec4cc90a82
-- title:
--   Chi: one eq sp Transl zero
-- statement:
--   The Chi construction uses the one eq sp Transl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OneEqSpTranslZero.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OneEqSpTranslZero.lean#L24-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.one_eq_spTransl_zero (g : ℕ) :
    (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = spTransl 0 := by sorry
