-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolFam_vtfLift
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolFam_vtfLift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:04:01.649067+00:00
-- url     : https://prove2.me/theorems/1f5d0f88-2bad-4021-92c1-a1341c245c9a
-- title:
--   Pullback Sections: is Hol Fam vtf Lift
-- statement:
--   The Pullback Sections construction uses the is Hol Fam vtf Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L207-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L207-L216

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolFam_vtfLift (hol : IsHolFam e) : IsHolFam (vtfLift f u e he) := by sorry
