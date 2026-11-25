-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_decomp
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.decomp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:50.957286+00:00
-- url     : https://prove2.me/theorems/391d19c0-0c45-4fd2-9526-1c628d885bb4
-- title:
--   Green Function: decomp
-- statement:
--   The Green Function construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L113-L115

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.decomp (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) :
    r * Real.log r * Δ u (a + r • ee θ) = Arad u a θ r + AngularPart u a r θ := by sorry
