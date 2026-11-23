-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_units
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:07.994366+00:00
-- url     : https://prove2.me/theorems/f90a1e6a-2a34-4abf-a88a-95bde2f4697b
-- title:
--   DVR: gen Has Val units
-- statement:
--   The DVR construction uses the gen Has Val units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L169-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L169-L189

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
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

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_units {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen ∧ ∃ c : FractionRing V, HasVal ϖ c n ∧
      ∀ j : Ix → L.ι, ∃ C : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ,
        C.val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) ∧
        (t.s j : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ) =
          C * res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)) := by sorry
