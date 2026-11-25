-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_cocycle
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.linComb_cocycle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:51.210799+00:00
-- url     : https://prove2.me/theorems/e046662b-94cc-5bf4-8f76-da6391623ae6
-- title:
--   DVR: lin Comb cocycle
-- statement:
--   The DVR construction uses the lin Comb cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L48-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L48-L73

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
set_option maxHeartbeats 1000000
include hL

theorem ReciprocityTheory.ChartRestriction.G.DVR.linComb_cocycle (i j l : K → L.ι) :
    res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ i ⊓ LB.wchart L φ j)
        ((LB.LinComb L φ ε).g i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ j ⊓ LB.wchart L φ l)
        ((LB.LinComb L φ ε).g j l) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ i ⊓ LB.wchart L φ l)
        ((LB.LinComb L φ ε).g i l) := by sorry
