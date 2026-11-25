-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_locallyCompactSpace_of_isLocalHomeomorph
-- name    : ReciprocityTheory.L2DbarEstimates.I.locallyCompactSpace_of_isLocalHomeomorph
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:35.594817+00:00
-- url     : https://prove2.me/theorems/6ec46297-f347-4d0b-9265-2200bc54c7a6
-- title:
--   I: locally Compact Space of is Local Homeomorph
-- statement:
--   The I construction uses the locally Compact Space of is Local Homeomorph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocallyCompactSpaceOfIsLocalHomeomorph.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocallyCompactSpaceOfIsLocalHomeomorph.lean#L25-L38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocallyCompactSpaceOfIsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.locallyCompactSpace_of_isLocalHomeomorph {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) : LocallyCompactSpace M := by sorry
