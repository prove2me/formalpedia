-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_one_of_zero
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gen_one_of_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:06:16.353488+00:00
-- url     : https://prove2.me/theorems/457896e6-62b9-4305-ab56-238f2300383a
-- title:
--   DVR: gen one of zero
-- statement:
--   The DVR construction uses the gen one of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L86-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L86-L133

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
open scoped Classical

theorem ReciprocityTheory.ChartRestriction.G.DVR.gen_one_of_zero (hGF : GlobalFnsSt) (D : DegData V (maximalIdeal V)) {K : Type} [Fintype K]
    (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen) (h0 : fsum φ ε = 0)
    (hv : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L φ ε t (eSec D.toPre.P.A)) (LB.oneGen D.toPre.P.L)) :
    ∀ j, LB.Coh D.toPre.P.L φ j → t.s j = 1 := by sorry
