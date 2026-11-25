-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_prodU
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_prodU
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:43:32.705568+00:00
-- url     : https://prove2.me/theorems/51087736-70ee-546b-abb3-640cf0d3ed7c
-- title:
--   Pullback Sections: vtf val prod U
-- statement:
--   The Pullback Sections construction uses the vtf val prod U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L24-L29

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_prodU (p : Sp ℂ ⟶ Y) {V : Y.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : K → Γ(Y, V)ˣ) (ε : K → ℤ) :
    valAt' p V (∏ k, u k ^ ε k).val = ∏ k, valAt' p V (u k).val ^ ε k := by sorry
