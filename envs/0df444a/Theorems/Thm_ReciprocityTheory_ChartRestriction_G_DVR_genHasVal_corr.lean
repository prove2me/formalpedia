-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_corr
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_corr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:04.874382+00:00
-- url     : https://prove2.me/theorems/543cff8b-28ca-47e2-ade8-7e7707b856d3
-- title:
--   DVR: gen Has Val corr
-- statement:
--   The DVR construction uses the gen Has Val corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L252-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L252-L343

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_corr (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix Ix' : Type}
    [Fintype Ix] [Fintype Ix'] (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s]
    (φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k) (ε₁ : Ix → ℤ)
    (φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)) (φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) (ε₂ : Ix' → ℤ)
    (hs₁ : ∀ k, φ₁ k ≫ s = 𝟙 _) (hs₂ : ∀ k, φ₂ k ≫ s = 𝟙 _)
    (t₁ : LB.Gen (LB.LinComb L φ₁' ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂' ε₂)) (ht₂ : t₂.IsGen)
    (hc : LB.Gen.Corr L φ₁' ε₁ φ₂' ε₂ t₁ t₂) {n : ℤ} (hn : GenHasVal ϖ L φ₁ φ₁' hφ₁ ε₁ t₁ n) :
    GenHasVal ϖ L φ₂ φ₂' hφ₂ ε₂ t₂ n := by sorry
