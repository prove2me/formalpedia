-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_ang
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:32.844929+00:00
-- url     : https://prove2.me/theorems/c39a7682-076c-5c0b-878c-5edf089d38ee
-- title:
--   Green Function: has Deriv At ang
-- statement:
--   The Green Function construction uses the has Deriv At ang property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L82-L87

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_ang (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => u (a + r • ee θ))
      (fderiv ℝ u (a + r • ee θ) (r • (Complex.I * ee θ))) θ := by sorry
