-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_lap_vanish
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.lap_vanish
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:00.010902+00:00
-- url     : https://prove2.me/theorems/25881161-031d-478c-9f7c-3c0e51cefa2f
-- title:
--   Green Function: lap vanish
-- statement:
--   The Green Function construction uses the lap vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L229-L231

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section

theorem ReciprocityTheory.AnForm.A.GreenFunction.lap_vanish {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : Δ u z = 0 := by sorry
