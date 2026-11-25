-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_value
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_value
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:45.904853+00:00
-- url     : https://prove2.me/theorems/1cd1a925-a8d6-47c1-8d26-e5cd5f82789e
-- title:
--   DVR: exists value
-- statement:
--   The DVR construction uses the exists value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L85-L102

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
open scoped Classical

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_value (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (z : Z ⟶ Y) (h0 : fsum (fun k => z ≫ φ k) ε = 0) :
    ∃ c : Γ(Z, ⊤)ˣ, ∀ j : K → L.ι, LB.Coh L (fun k => z ≫ φ k) j →
      res (le_top : LB.wchart L (fun k => z ≫ φ k) j ≤ ⊤) c = (LB.pullGen L φ ε t z).s j := by sorry
