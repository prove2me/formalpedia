-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_countable
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtA_countable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:14.666896+00:00
-- url     : https://prove2.me/theorems/8c2bde62-4616-4886-a10d-a45938856f14
-- title:
--   T0: gt A countable
-- statement:
--   The T0 construction uses the gt A countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L7-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule

theorem ReciprocityTheory.ChartRestriction.G.T0.gtA_countable {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Countable (span ℤ (Set.range B)).toAddSubgroup := by sorry
