-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiAt_of_U
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.chiAt_of_U
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:17.215878+00:00
-- url     : https://prove2.me/theorems/39b17eb3-b6b6-58b1-bd6d-4d9e2179a1f1
-- title:
--   Chi: chi At of U
-- statement:
--   The Chi construction uses the chi At of U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L62-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.chiAt_of_U {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (h : ChiAtU g γ) :
    ChiAt g γ := by sorry
