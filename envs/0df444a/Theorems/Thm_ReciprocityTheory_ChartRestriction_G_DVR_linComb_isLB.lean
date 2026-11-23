-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:17.945031+00:00
-- url     : https://prove2.me/theorems/c042551a-af9c-4371-bfbb-95af1001c71e
-- title:
--   DVR: lin Comb is LB
-- statement:
--   The DVR construction uses the lin Comb is LB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L88-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
include hL

theorem ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB : (LB.LinComb L φ ε).IsLB := by sorry
