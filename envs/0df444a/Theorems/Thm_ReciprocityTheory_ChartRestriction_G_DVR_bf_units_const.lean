-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_bf_units_const
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.bf_units_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:06:17.745241+00:00
-- url     : https://prove2.me/theorems/6d8264d0-b1b4-50d9-9b84-956975f9aee0
-- title:
--   DVR: bf units const
-- statement:
--   The DVR construction uses the bf units const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L277-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L277-L306

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.bf_units_const (hGF : GlobalFnsSt) (hBC : PolBaseChangeSt) (f : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ) :
    ∃ c : Γ((TF (R := V) F).left, ⊤)ˣ,
      f = Units.map ((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom.toMonoidHom c := by sorry
