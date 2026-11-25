-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_of_top
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gen_of_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:14.941475+00:00
-- url     : https://prove2.me/theorems/19a6af5c-72ea-46f2-94c1-1c3a45039028
-- title:
--   DVR: gen of top
-- statement:
--   The DVR construction uses the gen of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L137-L146

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.gen_of_top (hL : L.IsLB) {S : Scheme.{0}} {W : Over S} (ψ : K → (W.left ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L (fun k => (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k) ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen := by sorry
