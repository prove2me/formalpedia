-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_mulGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_mulGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:47.470792+00:00
-- url     : https://prove2.me/theorems/5bf11c46-f246-46e3-99be-407f7f1426ea
-- title:
--   DVR: gen Has Val mul Gen
-- statement:
--   The DVR construction uses the gen Has Val mul Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L133-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L133-L208

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
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_mulGen (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix Ix' : Type} [Fintype Ix] [Fintype Ix']
    (φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k) (ε₁ : Ix → ℤ)
    (φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)) (φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) (ε₂ : Ix' → ℤ)
    (t₁ : LB.Gen (LB.LinComb L φ₁' ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂' ε₂)) {n m : ℤ}
    (hn : GenHasVal ϖ L φ₁ φ₁' hφ₁ ε₁ t₁ n) (hm : GenHasVal ϖ L φ₂ φ₂' hφ₂ ε₂ t₂ m) :
    GenHasVal ϖ L (Sum.elim φ₁ φ₂) (Sum.elim φ₁' φ₂') (sumElim_hφ hφ₁ hφ₂) (Sum.elim ε₁ ε₂)
      (LB.mulGen L φ₁' ε₁ φ₂' ε₂ t₁ t₂) (n + m) := by sorry
