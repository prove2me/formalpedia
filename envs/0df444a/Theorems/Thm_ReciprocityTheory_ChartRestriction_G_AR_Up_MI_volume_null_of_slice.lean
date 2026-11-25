-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_volume_null_of_slice
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.volume_null_of_slice
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:41.430148+00:00
-- url     : https://prove2.me/theorems/f73c0390-b6ec-508a-ab5b-fb7697cd25f2
-- title:
--   MI: volume null of slice
-- statement:
--   The MI construction uses the volume null of slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfC.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfC.lean#L9-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.volume_null_of_slice {I : Type*} [Fintype I] [DecidableEq I] (i0 : I) {S : Set (I → ℂ)}
    (hS : MeasurableSet S) (huniq : ∀ v ∈ S, ∀ v' ∈ S, (∀ j, j ≠ i0 → v j = v' j) → v = v') :
    volume S = 0 := by sorry
