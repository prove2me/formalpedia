-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_secRel_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.secRel_pull
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:06.592255+00:00
-- url     : https://prove2.me/theorems/2f9ab234-339f-53c1-8693-8c405ebab0d0
-- title:
--   DVR: sec Rel pull
-- statement:
--   The DVR construction uses the sec Rel pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L16-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L16-L50

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.secRel_pull (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι) (j₃ : K₃ → L.ι)
    (hcoh : LB.Coh L (Sum.elim φ₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃)) (Sum.elim j₁ (Sum.elim j₂ j₃)))
    (q : Z ⟶ Y') {O : Z.Opens}
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ₁ j₁) (h₂ : O ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂)
    (h₃ : O ≤ q ⁻¹ᵁ LB.wchart L φ₃ j₃) :
    rs h₁ ((q.app _).hom (s₁.f j₁)) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) * rs h₃ ((q.app _).hom (u.s j₃).val) := by sorry
