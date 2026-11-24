-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fsLp_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:58.064699+00:00
-- url     : https://prove2.me/theorems/9bf04f70-0db4-4915-b22c-5e084d7ab7cf
-- title:
--   Geo: fs Lp ne zero
-- statement:
--   The Geo construction uses the fs Lp ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L15-L20

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fsLp_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : fsLp ι z ≠ 0 := by sorry
