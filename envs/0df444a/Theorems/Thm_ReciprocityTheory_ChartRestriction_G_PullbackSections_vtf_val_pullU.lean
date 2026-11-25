-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_pullU
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_pullU
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:29:25.200497+00:00
-- url     : https://prove2.me/theorems/1c78a2c6-9239-5a4b-9d34-cb3ce44891c8
-- title:
--   Pullback Sections: vtf val pull U
-- statement:
--   The Pullback Sections construction uses the vtf val pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L42-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
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
variable {Z Z' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_pullU (p : Sp ℂ ⟶ Z) (f : Z ⟶ Z') (U : Z'.Opens) (u : Γ(Z', U)ˣ) :
    valAt' p (f ⁻¹ᵁ U) (pullU f U u : Γ(Z, f ⁻¹ᵁ U)) = valAt' (p ≫ f) U (u : Γ(Z', U)) := by sorry
