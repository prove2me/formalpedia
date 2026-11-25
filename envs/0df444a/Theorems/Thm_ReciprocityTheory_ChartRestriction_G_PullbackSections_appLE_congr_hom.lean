-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_appLE_congr_hom
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.appLE_congr_hom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:51:12.788745+00:00
-- url     : https://prove2.me/theorems/791d430d-dcec-538d-b5e5-d986ea3d54d5
-- title:
--   Pullback Sections: app LE congr hom
-- statement:
--   The Pullback Sections construction uses the app LE congr hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L134-L137

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
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
variable {Y : Scheme.{0}}
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.appLE_congr_hom {A : CommRingCat.{0}} {q q' : Spec A ⟶ Y} (hq : q = q') (U : Y.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U)
    (h' : ⊤ ≤ q' ⁻¹ᵁ U) : q.appLE U ⊤ h = q'.appLE U ⊤ h' := by sorry
