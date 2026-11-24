-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_expand_div_pow
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.expand_div_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:09.997402+00:00
-- url     : https://prove2.me/theorems/ba2fde02-658f-44f9-8ef2-071baacf8171
-- title:
--   TG: expand div pow
-- statement:
--   The TG construction uses the expand div pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L265-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L265-L286

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.expand_div_pow (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (n : ℕ) : ∀ (σ τ : H0 U.LG.L 1), (∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j) →
    ∀ (f : ∀ α, D.toPre.SecB 1 α), (∀ e, U.ExpandsAt e 1 σ f) →
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ (ϖ ^ n) * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by sorry
