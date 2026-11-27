-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_differentiableAt_fsGrad
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.differentiableAt_fsGrad
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:04.600844+00:00
-- url     : https://prove2.me/theorems/b4358d46-94dc-50e7-8c3a-b202f94b10dd
-- title:
--   Geo: differentiable At fs Grad
-- statement:
--   The Geo construction uses the differentiable At fs Grad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L54-L63

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.differentiableAt_fsGrad {z : ι → ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fsGrad (ι := ι)) z := by sorry
