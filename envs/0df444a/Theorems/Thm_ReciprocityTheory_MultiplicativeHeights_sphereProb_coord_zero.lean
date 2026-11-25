-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereProb_coord_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.sphereProb_coord_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:37.915011+00:00
-- url     : https://prove2.me/theorems/6285987a-6dfe-58ee-be7c-aa74ab7b6982
-- title:
--   Multiplicative Heights: sphere Prob coord zero
-- statement:
--   The Multiplicative Heights construction uses the sphere Prob coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L124-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L124-L153

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
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
open MeasureTheory Metric
open scoped Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.sphereProb_coord_zero {n : ℕ} (j : Fin n) :
    sphereProb n {z | spherePoint z j = 0} = 0 := by sorry
