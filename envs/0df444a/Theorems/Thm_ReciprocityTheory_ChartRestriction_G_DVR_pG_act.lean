-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pG_act
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pG_act
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:04.422811+00:00
-- url     : https://prove2.me/theorems/fa17b7ca-3a98-5363-b4c7-7ba46e6a5b64
-- title:
--   DVR: p G act
-- statement:
--   The DVR construction uses the p G act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L67-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L67-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
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

theorem ReciprocityTheory.ChartRestriction.G.DVR.pG_act {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG)
    (e : ℕ) (a : O) :
    ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
      (U.gt e).pG.left ≫ (ιD.onB.act a).left := by sorry
