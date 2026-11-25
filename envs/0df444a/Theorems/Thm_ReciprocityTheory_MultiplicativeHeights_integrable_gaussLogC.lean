-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_gaussLogC
-- name    : ReciprocityTheory.MultiplicativeHeights.integrable_gaussLogC
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:55.816801+00:00
-- url     : https://prove2.me/theorems/0083d9f4-5534-5e60-ae68-936b2e4e75a1
-- title:
--   Multiplicative Heights: integrable gauss Log C
-- statement:
--   The Multiplicative Heights construction uses the integrable gauss Log C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L142-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L142-L161

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

theorem ReciprocityTheory.MultiplicativeHeights.integrable_gaussLogC {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ log (a * ‖z‖) * exp (-‖z‖ ^ 2)) := by sorry
