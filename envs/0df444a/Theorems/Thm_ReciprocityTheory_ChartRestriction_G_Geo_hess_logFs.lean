-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_hess_logFs
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.hess_logFs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:47.762148+00:00
-- url     : https://prove2.me/theorems/4ca0daa0-a82c-4534-a72c-5582c5418bdb
-- title:
--   Geo: hess log Fs
-- statement:
--   The Geo construction uses the hess log Fs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L65-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean#L65-L84

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.hess_logFs {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => Real.log ‖fsLp ι z‖)) z w w =
      ‖fsLp ι w‖ ^ 2 / ‖fsLp ι z‖ ^ 2 -
        2 * inner ℝ (fsLp ι z) (fsLp ι w) ^ 2 / (‖fsLp ι z‖ ^ 2) ^ 2 := by sorry
