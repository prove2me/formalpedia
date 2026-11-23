-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_differentiableOn_tsum_loc
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:33.890944+00:00
-- url     : https://prove2.me/theorems/4d454c97-a2a2-48e2-b5dd-d1c305b8b0bd
-- title:
--   Poin Pf: differentiable On tsum loc
-- statement:
--   The Poin Pf construction uses the differentiable On tsum loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfA.lean#L107-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfA.lean#L107-L134

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {U : Set Y}
    (hU : IsOpen U) (f : ι → Y → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ y ∈ U, ∃ ε > 0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ v ∈ ball y ε, ‖f i v‖ ≤ u i) :
    DifferentiableOn ℂ (fun y => ∑' i, f i y) U := by sorry
