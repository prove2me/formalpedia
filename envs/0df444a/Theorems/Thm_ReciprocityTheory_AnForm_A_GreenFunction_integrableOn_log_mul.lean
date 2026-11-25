-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integrableOn_log_mul
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.integrableOn_log_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:05.97454+00:00
-- url     : https://prove2.me/theorems/f89e2318-bc7d-5a2e-8179-fc2e3ba1e6c4
-- title:
--   Green Function: integrable On log mul
-- statement:
--   The Green Function construction uses the integrable On log mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L190-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L190-L220

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

theorem ReciprocityTheory.AnForm.A.GreenFunction.integrableOn_log_mul {P : ℝ × ℝ → ℝ} (hP : Continuous P) {R : ℝ} (hR0 : 0 < R)
    (hz : ∀ p : ℝ × ℝ, R < p.1 → P p = 0) :
    IntegrableOn (fun p : ℝ × ℝ => Real.log p.1 * P p) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by sorry
