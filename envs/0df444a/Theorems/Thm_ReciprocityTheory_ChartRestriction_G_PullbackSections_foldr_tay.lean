-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_foldr_tay
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.foldr_tay
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:06.188605+00:00
-- url     : https://prove2.me/theorems/c5bf1987-4f05-599d-b520-54d5432d4968
-- title:
--   Pullback Sections: foldr tay
-- statement:
--   The Pullback Sections construction uses the foldr tay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L205-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L205-L211

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
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.foldr_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} (u : ι → Fin g → ℂ)
    (m : ι →₀ ℕ) (L : List ι) (s : Multiset (Fin g → ℂ)) :
    L.foldr (fun l f => (Dof (addF ℂ g) (u l))^[m l] f) (tay θ s) =
      tay θ ((L.map fun l => Multiset.replicate (m l) (u l)).sum + s) := by sorry
