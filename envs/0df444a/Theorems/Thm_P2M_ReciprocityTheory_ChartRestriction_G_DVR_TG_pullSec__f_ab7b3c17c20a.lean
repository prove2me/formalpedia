-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_pullSec__f_ab7b3c17c20a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_pullSec__f_ab7b3c17c20a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:32.00382+00:00
-- url     : https://prove2.me/theorems/65b4d94d-6ce8-4770-904b-46c127a8dd7d
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR TG pull Sec  f ab7b3c17c20a: P2 M Reciprocity Theory Chart Restriction G DVR TG pull Sec  f ab7b3c17c20a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR TG pull Sec  f ab7b3c17c20a construction uses the P2 M Reciprocity Theory Chart Restriction G DVR TG pull Sec  f ab7b3c17c20a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenGeneric.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenGeneric.lean#L24-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_pullSec__f_ab7b3c17c20a {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k)
    (j : K → L.ι) :
    (pullSec' L φ ε s h φ' hφ).f j =
      (Z.presheaf.map (homOfLE (wchart_le_preimage L h φ φ' hφ j)).op).hom ((h.app _).hom (s.f j)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«TG».«pullSec'_f» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_pullSec__f_ab7b3c17c20a
