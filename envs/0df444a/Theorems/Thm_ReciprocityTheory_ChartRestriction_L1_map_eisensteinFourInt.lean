-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_eisensteinFourInt
-- name    : ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:11.70964+00:00
-- url     : https://prove2.me/theorems/e37f3092-3392-4be6-aa0c-09d16dabbe93
-- title:
--   L1: map eisenstein Four Int
-- statement:
--   The L1 construction uses the map eisenstein Four Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEisInt.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEisInt.lean#L61-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by sorry
