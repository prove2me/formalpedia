-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_mink_pi_lt
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_lt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:47.824958+00:00
-- url     : https://prove2.me/theorems/d82e79bb-1e2f-481a-a8b8-091aef0d7587
-- title:
--   T0: gt A mink pi lt
-- statement:
--   The T0 construction uses the gt A mink pi lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L18-L34

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

theorem ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_lt {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (h : |(Matrix.of B).det| < t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ < t := by sorry
