-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_pullGen
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_pullGen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:38.16103+00:00
-- url     : https://prove2.me/theorems/1ccba8ff-3e5f-46d6-9e48-7d1196832c40
-- title:
--   Pullback Sections: vtf val pull Gen
-- statement:
--   The Pullback Sections construction uses the vtf val pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L50-L53

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (p : Sp ℂ ⟶ Z) (j : K → L.ι) (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j) :
    valAt' p _ ((LB.pullGen L φ ε c h).s j).val = valAt' (p ≫ h) _ (c.s j).val := by sorry
