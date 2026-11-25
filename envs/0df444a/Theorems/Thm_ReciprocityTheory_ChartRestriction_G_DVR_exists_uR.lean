-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_uR
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_uR
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:06.281784+00:00
-- url     : https://prove2.me/theorems/e39a18ae-b205-4326-a136-62b9ea3eb118
-- title:
--   DVR: exists u R
-- statement:
--   The DVR construction uses the exists u R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L135-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L135-L178

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_uR (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    (oa : D.toPre.OAct O) (a : O) :
    ∃ uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε),
      uR.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L) := by sorry
