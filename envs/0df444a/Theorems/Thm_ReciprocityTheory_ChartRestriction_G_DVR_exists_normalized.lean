-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_normalized
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_normalized
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:08.023938+00:00
-- url     : https://prove2.me/theorems/4474d176-b4de-4083-b455-94e4cf5b55fa
-- title:
--   DVR: exists normalized
-- statement:
--   The DVR construction uses the exists normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L117-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L117-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_normalized (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z) (h0 : fsum (fun k => z ≫ φ k) ε = 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      ∀ j : K → L.ι, LB.Coh L (fun k => z ≫ φ k) j → (LB.pullGen L φ ε t' z).s j = 1 := by sorry
