-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_gaussOneC
-- name    : ReciprocityTheory.MultiplicativeHeights.integrable_gaussOneC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:10.224698+00:00
-- url     : https://prove2.me/theorems/7271adc0-a0d9-4ef6-8fc5-959ff5e82599
-- title:
--   Multiplicative Heights: integrable gauss One C
-- statement:
--   The Multiplicative Heights construction uses the integrable gauss One C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L109-L114

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

theorem ReciprocityTheory.MultiplicativeHeights.integrable_gaussOneC : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by sorry
