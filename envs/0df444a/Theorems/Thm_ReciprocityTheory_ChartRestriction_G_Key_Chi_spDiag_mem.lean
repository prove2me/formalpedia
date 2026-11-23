-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:13.231972+00:00
-- url     : https://prove2.me/theorems/892b0cca-4672-4326-a0e4-21597a60b585
-- title:
--   Chi: sp Diag mem
-- statement:
--   The Chi construction uses the sp Diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean#L14-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_mem (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U ∈ spH g := by sorry
