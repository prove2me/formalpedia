-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullback_generator_isGenerator
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pullback_generator_isGenerator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:34.312994+00:00
-- url     : https://prove2.me/theorems/1eac7513-abc5-48ef-a8a9-5c625d1118b4
-- title:
--   DVR: pullback generator is Generator
-- statement:
--   The DVR construction uses the pullback generator is Generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L20-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L20-L57

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.pullback_generator_isGenerator {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Z ⟶ Y) (i j : K → L.ι) :
    res (inf_le_left : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
        (LB.LinComb L (fun k => h ≫ φ k) ε).U i) ((LB.pullGen L φ ε t h).s i) =
      (LB.LinComb L (fun k => h ≫ φ k) ε).g i j *
        res (inf_le_right : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
          (LB.LinComb L (fun k => h ≫ φ k) ε).U j) ((LB.pullGen L φ ε t h).s j) := by sorry
