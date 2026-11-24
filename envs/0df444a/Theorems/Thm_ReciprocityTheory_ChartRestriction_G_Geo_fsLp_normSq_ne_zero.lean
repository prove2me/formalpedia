-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_normSq_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fsLp_normSq_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:25.804537+00:00
-- url     : https://prove2.me/theorems/0c82ce27-0ef1-4b86-b2c7-9b815198c758
-- title:
--   Geo: fs Lp norm Sq ne zero
-- statement:
--   The Geo construction uses the fs Lp norm Sq ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L24-L24

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fsLp_normSq_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : ‖fsLp ι z‖ ^ 2 ≠ 0 := by sorry
