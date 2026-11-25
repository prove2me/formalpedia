-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusPts_charUnit_appTop
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.TorusPts.charUnit_appTop
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:58.655212+00:00
-- url     : https://prove2.me/theorems/57185e5b-8d10-4623-9886-f57e69232f23
-- title:
--   Torus Pts: char Unit app Top
-- statement:
--   The Torus Pts construction uses the char Unit app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GtPtsTor.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GtPtsTor.lean#L15-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.TorusPts
open TorusInj
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem ReciprocityTheory.ChartRestriction.G.Semi.TorusPts.charUnit_appTop {Z : Scheme.{0}} (τ : Z ⟶ (splitTorus S X).left) (χ : X) :
    τ.appTop.hom (charUnit S X χ).val =
      (τ ≫ tFst X).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by sorry
