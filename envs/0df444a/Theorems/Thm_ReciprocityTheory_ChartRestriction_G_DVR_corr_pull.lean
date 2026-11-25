-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.corr_pull
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:13.392472+00:00
-- url     : https://prove2.me/theorems/a38ea188-875d-41b9-941a-ed08ebace51a
-- title:
--   DVR: corr pull
-- statement:
--   The DVR construction uses the corr pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L52-L69

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.corr_pull (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (hj : LB.Coh L φ j)
    (hj' : LB.Coh L φ' j') (hjj : ∀ k k', φ k = φ' k' → j k = j' k')
    (q : Z ⟶ Y') {O : Z.Opens} (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ j) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' j') :
    rs h₁ ((q.app _).hom (t.s j).val) = rs h₂ ((q.app _).hom (t'.s j').val) := by sorry
