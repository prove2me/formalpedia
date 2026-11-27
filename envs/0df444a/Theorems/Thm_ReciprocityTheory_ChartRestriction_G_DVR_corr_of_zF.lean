-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_of_zF
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.corr_of_zF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:16:29.242424+00:00
-- url     : https://prove2.me/theorems/216b7599-821a-4110-98bb-a4cf57026125
-- title:
--   DVR: corr of z F
-- statement:
--   The DVR construction uses the corr of z F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L345-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L345-L421

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
open scoped Classical

theorem ReciprocityTheory.ChartRestriction.G.DVR.corr_of_zF (hGF : GlobalFnsSt) (hBC : PolBaseChangeSt) (hL : D.toPre.P.L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {φ' : K' → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb D.toPre.P.L φ' ε')) (ht' : t'.IsGen) (hs : LB.SameSum φ ε φ' ε')
    (hval : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L φ ε t (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L φ' ε' t' (DegPre.zF D.toPre F).left)) :
    LB.Gen.Corr D.toPre.P.L φ ε φ' ε' t t' := by sorry
