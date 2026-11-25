-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_product_generator_isGenerator
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.product_generator_isGenerator
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:11:12.577004+00:00
-- url     : https://prove2.me/theorems/017fba09-b584-4e32-b4d8-5d862e08cd2f
-- title:
--   DVR: product generator is Generator
-- statement:
--   The DVR construction uses the product generator is Generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L81-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L81-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
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
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.DVR.product_generator_isGenerator {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen)
    (i j : K ⊕ K' → L.ι) :
    res (inf_le_left : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓
        (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i)
        ((LB.mulGen L φ ε φ' ε' t t').s i) =
      (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j *
        res (inf_le_right : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓
          (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j)
          ((LB.mulGen L φ ε φ' ε' t t').s j) := by sorry
