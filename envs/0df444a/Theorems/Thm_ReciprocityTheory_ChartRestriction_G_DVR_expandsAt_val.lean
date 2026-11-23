-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expandsAt_val
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:43.379353+00:00
-- url     : https://prove2.me/theorems/d6d22ccf-cfe5-4c7f-90d4-76b3cc916cef
-- title:
--   DVR: expands At val
-- statement:
--   The DVR construction uses the expands At val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean#L89-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean#L89-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
variable (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)

theorem ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val (h : U.ExpandsAt e k σ f) : ∃ S : Finset D.toPre.X, ∀ (Z : Scheme.{0})
    (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      (∀ α ∉ S, sval (f α) (r ≫ (pGl U e)) z J = 0) ∧ ∀ jL, (fGl I G e) (r z) ∈ U.LG.L.U jL →
      (wv U e r z (J (r ≫ (pGl U e))) jL ^ k).val * sv U k σ (r ≫ (fGl I G e)) z jL =
        ∑ α ∈ S, sval (f α) (r ≫ (pGl U e)) z J * (val (tG U e α) r z J).val := by sorry
