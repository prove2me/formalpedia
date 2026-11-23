-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:53.957222+00:00
-- url     : https://prove2.me/theorems/2ef2da6e-3427-4bb5-8db1-6b353ca7d786
-- title:
--   Chi: cols Fixed mul
-- statement:
--   The Chi construction uses the cols Fixed mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean#L18-L27

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_mul {k : ℕ} {O M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hO : ColsFixed k O) (hM : ColsFixed k M) : ColsFixed k (O * M) := by sorry
