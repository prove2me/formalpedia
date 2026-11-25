-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_expandsAt_of_div
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.expandsAt_of_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:53.410828+00:00
-- url     : https://prove2.me/theorems/57e33459-1e49-5a99-b4fe-68ee7709b069
-- title:
--   TG: expands At of div
-- statement:
--   The TG construction uses the expands At of div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L71-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L71-L195

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
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.expandsAt_of_div (U : UnifPre I D A G) [Flat G.hom] {ϖ : R} (hϖ : ϖ ≠ 0) (hI : I = Ideal.span {ϖ})
    (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f g : ∀ α, D.toPre.SecB 1 α) (hfg : ∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt (e + 1) 1 σ f) : U.ExpandsAt e 1 τ g := by sorry
