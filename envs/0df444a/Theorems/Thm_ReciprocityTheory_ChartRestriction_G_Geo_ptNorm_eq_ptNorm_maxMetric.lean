-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_ptNorm_eq_ptNorm_maxMetric
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_eq_ptNorm_maxMetric
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:04.242119+00:00
-- url     : https://prove2.me/theorems/43b178a9-eb94-47b4-9722-0dcf1efb461a
-- title:
--   Geo: pt Norm eq pt Norm max Metric
-- statement:
--   The Geo construction uses the pt Norm eq pt Norm max Metric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L70-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
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
open MvPolynomial
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_eq_ptNorm_maxMetric (h : ConeMetric C ι) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) {z : ι → C} (heq : ‖z‖ = h.ρ z) :
    ptNorm h σ d f z = ptNorm (maxMetric C ι) σ d f z := by sorry
