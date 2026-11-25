-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_mD_cons_sum
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.mD_cons_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:58.45146+00:00
-- url     : https://prove2.me/theorems/1ed04f8e-4c87-4d71-a51d-465a73c4b258
-- title:
--   Pullback Sections: m D cons sum
-- statement:
--   The Pullback Sections construction uses the m D cons sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L98-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.mD_cons_sum {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) {ι : Type} (t : Finset ι) (c : ι → ℂ)
    (w : ι → V) (s : Multiset V) :
    mD φ x ((∑ i ∈ t, c i • w i) ::ₘ s) = ∑ i ∈ t, c i * mD φ x (w i ::ₘ s) := by sorry
