-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_rad
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:27.758433+00:00
-- url     : https://prove2.me/theorems/6991d15f-f33d-4316-a32c-a6b151d4e1c1
-- title:
--   Green Function: has Deriv At rad
-- statement:
--   The Green Function construction uses the has Deriv At rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L68-L72

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
variable {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ)
include hu

theorem ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_rad (e : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => u (a + r • e)) (fderiv ℝ u (a + r • e) e) r := by sorry
