-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_pullGen_of
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_pullGen_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:06.624397+00:00
-- url     : https://prove2.me/theorems/9b7ee504-9ecf-4f3d-868a-f022b9576c83
-- title:
--   DVR: gen Has Val pull Gen of
-- statement:
--   The DVR construction uses the gen Has Val pull Gen of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L345-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L345-L370

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_pullGen_of {X Y : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix] (φ : Ix → (Y ⟶ X))
    (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Spec (CommRingCat.of V) ⟶ Y)
    (q : Spec (CommRingCat.of (FractionRing V)) ⟶ Y) (hq : q = jK V ≫ p) :
    GenHasVal ϖ L (fun k => p ≫ φ k) (fun k => q ≫ φ k) (fun k => by rw [hq, Category.assoc]) ε
      (LB.pullGen L φ ε t q) 0 := by sorry
