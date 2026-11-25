-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_unit_normB
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.unit_normB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:15.775399+00:00
-- url     : https://prove2.me/theorems/b378d6c8-e9c0-509e-b4fc-cbf77fb11e25
-- title:
--   Gt BCPf: unit norm B
-- statement:
--   The Gt BCPf construction uses the unit norm B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitNorm.lean#L85-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitNorm.lean#L85-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitNorm
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)
attribute [local instance] SplitExt.free SplitExt.finite
variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.unit_normB (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X) :
    res (inf_le_left : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j))
        (pullU (eSec ((Over.pullback f).obj G)) _ (uB f E d j k)) *
      res (inf_le_right : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k))
        (((pullExt f E).O ((pullExt f E).basis k)).rig.s (fun _ => j k)) = 1 := by sorry
