-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_expandsAt_scale
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.expandsAt_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:16.722805+00:00
-- url     : https://prove2.me/theorems/4c7f4994-9b65-48d2-b517-61d5e4c0aed3
-- title:
--   TG: expands At scale
-- statement:
--   The TG construction uses the expands At scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L217-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L217-L236

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.expandsAt_scale (U : UnifPre I D A G) (c : R) (τ τ' : H0 U.LG.L 1)
    (hτ : ∀ j, τ'.f j = toW G.hom _ c * τ.f j)
    (g g' : ∀ α, D.toPre.SecB 1 α) (hg : ∀ α j, (g' α).f j = toW D.toPre.P.A.hom _ c * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt e 1 τ g) : U.ExpandsAt e 1 τ' g' := by sorry
