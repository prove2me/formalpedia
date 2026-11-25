-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_equivB
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.equivB
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:12.082179+00:00
-- url     : https://prove2.me/theorems/471df070-05d9-4e5c-8b34-36bf8dd3c93c
-- title:
--   Gt BCPf: equiv B
-- statement:
--   The Gt BCPf construction uses the equiv B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L170-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L170-L195

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
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
attribute [local instance] SplitExt.free SplitExt.finite
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S) {G : Over S} [GrpObj G] (d : E.GtDatum G)

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.equivB : ∀ (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X),
    res (actB_le f E d j)
        (pullU (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
            μ[(Over.pullback f).obj G]).left _ (uB f E d j k)) =
      res (fun x _ => show (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left.base x ∈
          (⊤ : TopologicalSpace.Opens _) from trivial)
          (pullU (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⊤
            (charUnit S' (pullExt f E).X ((pullExt f E).basis k))) *
        pullU (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left _ (uB f E d j k) := by sorry
