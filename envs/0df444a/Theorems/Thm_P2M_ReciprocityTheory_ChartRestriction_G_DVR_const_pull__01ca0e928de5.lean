-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_const_pull__01ca0e928de5
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_const_pull__01ca0e928de5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:47:44.356423+00:00
-- url     : https://prove2.me/theorems/17510249-d3fd-4040-828b-6e09ba1a11f6
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR const pull  01ca0e928de5: P2 M Reciprocity Theory Chart Restriction G DVR const pull  01ca0e928de5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR const pull  01ca0e928de5 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR const pull  01ca0e928de5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L36-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
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
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_const_pull__01ca0e928de5 {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of R)) (pZ : Z ⟶ Spec (CommRingCat.of R))
    (hφ : φ ≫ pZ = pY) (r : R) {U : Z.Opens} {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U (scal pZ r))) = resTop W (scal pY r) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«const_pull'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_const_pull__01ca0e928de5
