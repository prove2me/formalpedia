-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_mulGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.rs_app_mulGen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:44.258388+00:00
-- url     : https://prove2.me/theorems/d6ee4bcd-f3ed-5440-b7ea-22ce8824d488
-- title:
--   DVR: rs app mul Gen
-- statement:
--   The DVR construction uses the rs app mul Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L77-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L77-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
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
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {X Y Y' Z : Scheme.{0}} (L : LB X) {K₁ K₂ K₃ K K' : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
  [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.rs_app_mulGen (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (q : Z ⟶ Y') {O : Z.Opens} (h : O ≤ q ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j)
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl)) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' (j ∘ Sum.inr)) :
    rs h ((q.app _).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val) =
      rs h₁ ((q.app _).hom (t.s (j ∘ Sum.inl)).val) * rs h₂ ((q.app _).hom (t'.s (j ∘ Sum.inr)).val) := by sorry
