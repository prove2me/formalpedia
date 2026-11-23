-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_fsum
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gs_fsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:31.734813+00:00
-- url     : https://prove2.me/theorems/ae26a7f8-e3b5-4677-8e50-47ea6fbaad69
-- title:
--   DVR: gs fsum
-- statement:
--   The DVR construction uses the gs fsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean#L18-L19

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.gs_fsum {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(X, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by sorry
