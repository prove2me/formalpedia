-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_closure
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_closure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:36.358035+00:00
-- url     : https://prove2.me/theorems/0b2fecb4-f009-4330-98ae-89ffc9ea922d
-- title:
--   Chi: chi U closure
-- statement:
--   The Chi construction uses the chi U closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OneEqSpTranslZero.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OneEqSpTranslZero.lean#L28-L37

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_closure {g : ℕ} (hInv : InversionStatement)
    {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hγ : γ ∈ Submonoid.closure (spGens g)) :
    γ ∈ Matrix.symplecticGroup (Fin g) ℤ ∧ ChiAtU g γ := by sorry
