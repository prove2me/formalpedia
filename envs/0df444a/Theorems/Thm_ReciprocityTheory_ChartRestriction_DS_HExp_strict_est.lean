-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_strict_est
-- name    : ReciprocityTheory.ChartRestriction.DS.HExp.strict_est
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:33.722301+00:00
-- url     : https://prove2.me/theorems/efc7b992-0da3-4033-a58e-75d6d2dd0f3b
-- title:
--   HExp: strict est
-- statement:
--   The HExp construction uses the strict est property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L85-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem ReciprocityTheory.ChartRestriction.DS.HExp.strict_est {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by sorry
