-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_g
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_g
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:31.221091+00:00
-- url     : https://prove2.me/theorems/34bc3da6-02a5-482d-af3b-d4169d4b4813
-- title:
--   Pullback Sections: vtf val g
-- statement:
--   The Pullback Sections construction uses the vtf val g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L100-L108

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
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_g {k : ℤ} (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (i i' : Fin 1 → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U i ⊓ (LPow A L k (Over.mk x0)).U i')) :
    valAt' p _ ((LPow A L k (Over.mk x0)).g i i').val =
      valAt' (p ≫ (snd (Over.mk x0) A).left) (L.U (i 0) ⊓ L.U (i' 0)) (L.g (i 0) (i' 0)).val ^ k := by sorry
