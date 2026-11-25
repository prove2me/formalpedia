-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_lap_eq_rot
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.lap_eq_rot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:50.579664+00:00
-- url     : https://prove2.me/theorems/6f9e6984-dbcc-4138-98ec-abf0284d8b04
-- title:
--   Green Function: lap eq rot
-- statement:
--   The Green Function construction uses the lap eq rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L46-L54

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.lap_eq_rot (u : ℂ → ℝ) (z : ℂ) (θ : ℝ) :
    Δ u z = fderiv ℝ (fderiv ℝ u) z (ee θ) (ee θ)
      + fderiv ℝ (fderiv ℝ u) z (Complex.I * ee θ) (Complex.I * ee θ) := by sorry
