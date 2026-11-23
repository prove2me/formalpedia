-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_norm_rad
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.norm_rad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:50.778816+00:00
-- url     : https://prove2.me/theorems/4ea14393-083b-4e12-adaa-5e1e4e176ec0
-- title:
--   Green Function: norm rad
-- statement:
--   The Green Function construction uses the norm rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L129-L130

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.norm_rad (a : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖a + r • ee θ - a‖ = r := by sorry
