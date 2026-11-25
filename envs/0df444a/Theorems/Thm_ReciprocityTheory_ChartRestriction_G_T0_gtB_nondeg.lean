-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtB_nondeg
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtB_nondeg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:42.966819+00:00
-- url     : https://prove2.me/theorems/4c7e05ab-1752-51df-b079-0b5945f25cda
-- title:
--   T0: gt B nondeg
-- statement:
--   The T0 construction uses the gt B nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L75-L85

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

theorem ReciprocityTheory.ChartRestriction.G.T0.gtB_nondeg (n : ℕ) : (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate := by sorry
