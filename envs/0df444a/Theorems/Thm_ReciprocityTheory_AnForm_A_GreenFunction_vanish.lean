-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_vanish
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.vanish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:05.779816+00:00
-- url     : https://prove2.me/theorems/328d9be4-d949-43e7-a6bc-2ed7b3887460
-- title:
--   Green Function: vanish
-- statement:
--   The Green Function construction uses the vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L117-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L117-L127

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.vanish {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : fderiv ℝ u z = 0 ∧ fderiv ℝ (fderiv ℝ u) z = 0 := by sorry
