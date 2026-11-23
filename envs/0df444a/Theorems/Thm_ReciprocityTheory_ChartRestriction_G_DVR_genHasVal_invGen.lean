-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_invGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_invGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:45.761313+00:00
-- url     : https://prove2.me/theorems/8ce7ba52-525e-43d4-89b0-c3bc1d9a5be6
-- title:
--   DVR: gen Has Val inv Gen
-- statement:
--   The DVR construction uses the gen Has Val inv Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L210-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L210-L250

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_invGen {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    GenHasVal ϖ L φ φ' hφ (fun k => - ε k) (LB.invGen L φ' ε t) (-n) := by sorry
