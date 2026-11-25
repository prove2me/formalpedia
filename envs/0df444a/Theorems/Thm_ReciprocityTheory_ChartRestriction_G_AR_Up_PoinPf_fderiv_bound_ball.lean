-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_fderiv_bound_ball
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.fderiv_bound_ball
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:33.862046+00:00
-- url     : https://prove2.me/theorems/2fc58d25-ede3-5ec6-bc0b-1a191c55ecc8
-- title:
--   Poin Pf: fderiv bound ball
-- statement:
--   The Poin Pf construction uses the fderiv bound ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfA.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfA.lean#L102-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open Metric

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.fderiv_bound_ball {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
    {R M : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball y (2 * R)))
    (hM : ∀ v ∈ ball y (2 * R), ‖g v‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / R := by sorry
