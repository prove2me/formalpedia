-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_spDiag_rk
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_spDiag_rk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:39.822316+00:00
-- url     : https://prove2.me/theorems/575d235a-0abe-4c31-a4f3-65141c5cd9f2
-- title:
--   Chi: cols Fixed sp Diag rk
-- statement:
--   The Chi construction uses the cols Fixed sp Diag rk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L174-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L174-L180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_spDiag_rk {k : ℕ} {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0)
    (hu : ∀ i : Fin g, (i : ℕ) < k → u i = 0) (hv : ∀ i : Fin g, (i : ℕ) < k → v i = 0) :
    ColsFixed k (spDiag (rkU u v h)) := by sorry
