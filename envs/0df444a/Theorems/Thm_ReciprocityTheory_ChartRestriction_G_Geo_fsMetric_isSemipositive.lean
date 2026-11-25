-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsMetric_isSemipositive
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fsMetric_isSemipositive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:25.903048+00:00
-- url     : https://prove2.me/theorems/735477ae-0d41-4002-b1e0-5d71fb6bd901
-- title:
--   Geo: fs Metric is Semipositive
-- statement:
--   The Geo construction uses the fs Metric is Semipositive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L122-L129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.Geo.fsMetric_isSemipositive : IsSemipositive (fsMetric ι) := by sorry
