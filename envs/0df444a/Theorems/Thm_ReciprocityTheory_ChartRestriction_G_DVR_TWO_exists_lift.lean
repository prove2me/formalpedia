-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_exists_lift
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TWO.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:14.63997+00:00
-- url     : https://prove2.me/theorems/f16c7707-3f11-43b7-8c29-9450ca1a36aa
-- title:
--   TWO: exists lift
-- statement:
--   The TWO construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean#L110-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean#L110-L123

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWO
open ReciprocityTheory.ChartRestriction.G.Out
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]

theorem ReciprocityTheory.ChartRestriction.G.DVR.TWO.exists_lift (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsProper p] (x : Spec (CommRingCat.of F) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom algVF)) :
    ∃ x' : Spec (CommRingCat.of (Ov v)) ⟶ X, x' ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x' = x := by sorry
