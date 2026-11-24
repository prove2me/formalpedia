-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_circle_fubini
-- name    : ReciprocityTheory.AnForm.A.circle_fubini
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:03.46306+00:00
-- url     : https://prove2.me/theorems/79420966-2243-475e-b7cf-d9176a8d4787
-- title:
--   A: circle fubini
-- statement:
--   The A construction uses the circle fubini property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L39-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L39-L89

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.circle_fubini {Φ : (Fin D → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦi : Integrable Φ)
    {k : (Fin D → ℂ) → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    {P : ℂ → (Fin D → ℂ) → (Fin D → ℂ)} (hP : Continuous (Function.uncurry P))
    (hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (P ζ) ∧ MeasurableEmbedding (P ζ)) :
    Integrable (fun y => k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1) ∧
    ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by sorry
