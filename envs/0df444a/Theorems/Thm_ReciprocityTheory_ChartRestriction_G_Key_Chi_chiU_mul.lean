-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:39.069334+00:00
-- url     : https://prove2.me/theorems/8bfc2fbd-6349-40ec-803c-22e88ef8c1ff
-- title:
--   Chi: chi U mul
-- statement:
--   The Chi construction uses the chi U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OneEqSpTranslZero.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OneEqSpTranslZero.lean#L9-L22

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_mul {g : ℕ} {x y : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hx : x ∈ Matrix.symplecticGroup (Fin g) ℤ) (hy : y ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (Hx : ChiAtU g x) (Hy : ChiAtU g y) : ChiAtU g (x * y) := by sorry
