-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtB_inner_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtB_inner_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:42.762793+00:00
-- url     : https://prove2.me/theorems/7c125d79-9a96-5b24-ba32-0775ee26ab7a
-- title:
--   T0: gt B inner eq
-- statement:
--   The T0 construction uses the gt B inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L69-L73

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

theorem ReciprocityTheory.ChartRestriction.G.T0.gtB_inner_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, EuclideanSpace.equiv (Fin n) ℝ x k * EuclideanSpace.equiv (Fin n) ℝ y k := by sorry
