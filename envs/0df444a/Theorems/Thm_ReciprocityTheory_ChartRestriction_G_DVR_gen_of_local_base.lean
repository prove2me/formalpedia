-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_of_local_base
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gen_of_local_base
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:41.075841+00:00
-- url     : https://prove2.me/theorems/7bd2dc5e-dd61-4eea-b2d7-f8a4b093216c
-- title:
--   DVR: gen of local base
-- statement:
--   The DVR construction uses the gen of local base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L148-L155

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.gen_of_local_base {V : Type} [CommRing V] [IsLocalRing V] (hL : L.IsLB)
    {W : Over (Spec (CommRingCat.of V))} (ψ : K → (W.left ⟶ X)) (ε : K → ℤ)
    (h : ∀ s : Spec (CommRingCat.of V), ∃ U : (Spec (CommRingCat.of V)).Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (W.hom ⁻¹ᵁ U).ι ≫ ψ k) ε), t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen := by sorry
