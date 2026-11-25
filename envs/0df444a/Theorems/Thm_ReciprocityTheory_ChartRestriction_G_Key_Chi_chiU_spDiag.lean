-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_spDiag
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_spDiag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:50.447592+00:00
-- url     : https://prove2.me/theorems/d9bb4e97-95ba-47a6-8e55-4f424bb5279f
-- title:
--   Chi: chi U sp Diag
-- statement:
--   The Chi construction uses the chi U sp Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L146-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L146-L178

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : ChiAtU g (spDiag U) := by sorry
