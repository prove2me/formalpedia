-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_volumeIoiPow
-- name    : ReciprocityTheory.MultiplicativeHeights.integrable_volumeIoiPow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:10.483651+00:00
-- url     : https://prove2.me/theorems/059c5b18-5d36-4c3b-bd2f-f30b04f80193
-- title:
--   Multiplicative Heights: integrable volume Ioi Pow
-- statement:
--   The Multiplicative Heights construction uses the integrable volume Ioi Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L19-L27

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real

theorem ReciprocityTheory.MultiplicativeHeights.integrable_volumeIoiPow {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by sorry
