-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_g_self
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.linComb_g_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:05.563225+00:00
-- url     : https://prove2.me/theorems/17f274f6-7a7f-523a-9c3e-e4891a310707
-- title:
--   DVR: lin Comb g self
-- statement:
--   The DVR construction uses the lin Comb g self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L38-L44

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.linComb_g_self (j : K → L.ι) :
    res (le_inf le_rfl le_rfl : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j j) = 1 := by sorry
