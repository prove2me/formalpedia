-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsMetric_fin_isSemipositive
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fsMetric_fin_isSemipositive
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:10.062123+00:00
-- url     : https://prove2.me/theorems/29ba96ba-4e8d-532a-8dd0-dcbd5505f5a8
-- title:
--   Geo: fs Metric fin is Semipositive
-- statement:
--   The Geo construction uses the fs Metric fin is Semipositive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L131-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L131-L131

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fsMetric_fin_isSemipositive (n : ℕ) : IsSemipositive (fsMetric (Fin n)) := by sorry
