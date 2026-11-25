-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_sum_degree
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sum_degree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:30.43057+00:00
-- url     : https://prove2.me/theorems/2dcd2105-9c61-5fe9-9b2b-dd9fc66cdfa4
-- title:
--   Wick Vanishing: sum degree
-- statement:
--   The Wick Vanishing construction uses the sum degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean#L63-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sum_degree {σ : Type} [Fintype σ] (n : σ →₀ ℕ) : n.degree = ∑ s, 1 * n s := by sorry
