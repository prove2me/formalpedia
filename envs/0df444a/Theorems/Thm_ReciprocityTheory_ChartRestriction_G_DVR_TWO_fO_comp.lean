-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TWO.fO_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:14.494803+00:00
-- url     : https://prove2.me/theorems/6dcc9a78-24a0-48aa-8e13-03f926bac6c3
-- title:
--   TWO: f O comp
-- statement:
--   The TWO construction uses the f O comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean#L96-L97

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TWO.fO_comp (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) :
    (algebraMap (Ov v) F).comp (fO v hϖ hv) = algVF := by sorry
