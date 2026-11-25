-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_comp_anLin
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetOf_comp_anLin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:10.337565+00:00
-- url     : https://prove2.me/theorems/8c51bc53-015d-4eef-ab93-25c6375c2053
-- title:
--   Pullback Sections: jet Of comp an Lin
-- statement:
--   The Pullback Sections construction uses the jet Of comp an Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L71-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {g g' : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetOf_comp_anLin (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0)
    (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) :
    jetOf m (θ ∘ A) = jetMap (anLin A) (anLin_mem A) (jetOf m θ) := by sorry
