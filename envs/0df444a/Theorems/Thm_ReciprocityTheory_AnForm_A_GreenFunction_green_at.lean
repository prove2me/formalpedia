-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_green_at
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.green_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:08.465801+00:00
-- url     : https://prove2.me/theorems/4600848a-929d-4e77-a8d0-8e2e0e21d1de
-- title:
--   Green Function: green at
-- statement:
--   The Green Function construction uses the green at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L252-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L252-L309

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.green_at {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z - a‖ * Δ u z = 2 * Real.pi * u a := by sorry
