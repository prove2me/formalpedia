-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_tay_comp_anLin
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.tay_comp_anLin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:42:38.120515+00:00
-- url     : https://prove2.me/theorems/bab7d33d-f830-5ab6-bf53-a9768d4ecee3
-- title:
--   Pullback Sections: tay comp an Lin
-- statement:
--   The Pullback Sections construction uses the tay comp an Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L45-L69

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.tay_comp_anLin {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) :
    tay (θ ∘ A) 0 = MvPowerSeries.subst (fun p => ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) :
      MvPowerSeries (Fin 1 × Fin g') ℂ)) (tay θ 0) := by sorry
