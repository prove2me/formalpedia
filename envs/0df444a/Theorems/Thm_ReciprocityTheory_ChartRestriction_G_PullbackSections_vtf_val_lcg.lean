-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_lcg
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_lcg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:31.144884+00:00
-- url     : https://prove2.me/theorems/df7b4a97-347e-4b4c-80c0-457b95a40806
-- title:
--   Pullback Sections: vtf val lcg
-- statement:
--   The Pullback Sections construction uses the vtf val lcg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L31-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by sorry
