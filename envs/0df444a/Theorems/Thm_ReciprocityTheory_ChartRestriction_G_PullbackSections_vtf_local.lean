-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_local
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_local
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:00:31.575547+00:00
-- url     : https://prove2.me/theorems/7a437937-76d4-47d1-9776-0b94dd78e8fa
-- title:
--   Pullback Sections: vtf local
-- statement:
--   The Pullback Sections construction uses the vtf local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L61-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L61-L205

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
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
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
variable {g : ℕ} {X Y : Scheme.{0}} (f : Y ⟶ X) (u : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
  (he : ∀ z, e z ≫ f = u)
set_option maxHeartbeats 800000

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_local (hol : IsHolFam e) (V : (pullback f u).Opens) (φ : Γ(pullback f u, V))
    (z0 : Fin g → ℂ) (hz0 : ⊤ ≤ vtfLift f u e he z0 ⁻¹ᵁ V) :
    ∃ N : Set (Fin g → ℂ), IsOpen N ∧ z0 ∈ N ∧ (∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V) ∧
      DifferentiableOn ℂ (fun z => valAt' (vtfLift f u e he z) V φ) N := by sorry
