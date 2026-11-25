-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_smul_I
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.fsLp_smul_I
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:40.752018+00:00
-- url     : https://prove2.me/theorems/e5bd9524-8c07-4dc8-9df1-d0981557e1d7
-- title:
--   Geo: fs Lp smul I
-- statement:
--   The Geo construction uses the fs Lp smul I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L22-L22

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.fsLp_smul_I (w : ι → ℂ) : fsLp ι (Complex.I • w) = Complex.I • fsLp ι w := by sorry
