-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_logA_exp
-- name    : ReciprocityTheory.ChartRestriction.DS.HExp.logA_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:15.170063+00:00
-- url     : https://prove2.me/theorems/053214a9-4ec0-4916-b0f6-2573e4136902
-- title:
--   HExp: log A exp
-- statement:
--   The HExp construction uses the log A exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L19-L20

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

theorem ReciprocityTheory.ChartRestriction.DS.HExp.logA_exp : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X := by sorry
