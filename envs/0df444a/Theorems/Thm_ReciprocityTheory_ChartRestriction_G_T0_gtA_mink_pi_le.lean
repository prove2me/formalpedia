-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_mink_pi_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:51.202685+00:00
-- url     : https://prove2.me/theorems/57e7c1ca-300e-4d52-a5a2-be1d7b5dff1e
-- title:
--   T0: gt A mink pi le
-- statement:
--   The T0 construction uses the gt A mink pi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L36-L54

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

theorem ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le {n : ℕ} (hn : 0 < n) (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) (h : |(Matrix.of B).det| ≤ t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ ≤ t := by sorry
