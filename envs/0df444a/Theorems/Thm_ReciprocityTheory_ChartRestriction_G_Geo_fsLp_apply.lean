-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fsLp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:25.469244+00:00
-- url     : https://prove2.me/theorems/488d1e27-5585-440e-b367-2a0e434e10b4
-- title:
--   Geo: fs Lp apply
-- statement:
--   The Geo construction uses the fs Lp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L13-L13

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fsLp_apply (z : ι → ℂ) : fsLp ι z = WithLp.toLp 2 z := by sorry
