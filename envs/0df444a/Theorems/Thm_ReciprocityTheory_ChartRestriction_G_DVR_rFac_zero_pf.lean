-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rFac_zero_pf
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.rFac_zero_pf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:52.277328+00:00
-- url     : https://prove2.me/theorems/78dbd1f5-a1e3-4b34-bb68-2d1ef4c011b9
-- title:
--   DVR: r Fac zero pf
-- statement:
--   The DVR construction uses the r Fac zero pf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RValuePf.lean#L43-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RValuePf.lean#L43-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValuePf
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem ReciprocityTheory.ChartRestriction.G.DVR.rFac_zero_pf (oa : D.toPre.OAct O) (a : O)
    (uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (huR : uR.IsGen)
    (hn : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (χ : D.toPre.X) :
    LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ (rFac D F oa a uR χ) (DegPre.zF D.toPre F).left) (LB.oneGen D.toPre.P.L) := by sorry
