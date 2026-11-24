-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_kp
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.kp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:19.162019+00:00
-- url     : https://prove2.me/theorems/3addb1d1-99a7-4907-8c62-82ea8f6e56f9
-- title:
--   TLin Pf: kp
-- statement:
--   The TLin Pf construction uses the kp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/FnOfComp.lean#L54-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/FnOfComp.lean#L54-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.kp (ρ : Γ((thickObj R I e G).left, ⊤))
    (h : (WeightPf.act g).left.appTop.hom ρ =
      (snd (WeightPf.Te D I e) (thickObj R I e G)).left.appTop.hom ρ)
    {Z : Scheme.{0}} (y1 y2 : Z ⟶ (thickObj R I e G).left) (hq : y1 ≫ g.q.left = y2 ≫ g.q.left) :
    y1.appTop.hom ρ = y2.appTop.hom ρ := by sorry
