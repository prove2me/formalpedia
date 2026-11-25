-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_scale
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetOf_scale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:15:50.567637+00:00
-- url     : https://prove2.me/theorems/70d3a179-18ab-5c15-b50e-bd93d068c6cd
-- title:
--   Pullback Sections: jet Of scale
-- statement:
--   The Pullback Sections construction uses the jet Of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L137-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L137-L150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetOf_scale (m : ℕ) (c : Fin g → ℂ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) :
    jetOf m (fun z => θ fun i => c i * z i) = jetScaleP m c (jetOf m θ) := by sorry
