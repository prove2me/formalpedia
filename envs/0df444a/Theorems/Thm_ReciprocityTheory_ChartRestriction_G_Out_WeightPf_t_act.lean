-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_t_act
-- name    : ReciprocityTheory.ChartRestriction.G.Out.WeightPf.t_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:25.860803+00:00
-- url     : https://prove2.me/theorems/57f0b27c-aad8-4a1c-85d8-cf72ed64c740
-- title:
--   Weight Pf: t act
-- statement:
--   The Weight Pf construction uses the t act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean#L146-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean#L146-L183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem ReciprocityTheory.ChartRestriction.G.Out.WeightPf.t_act (χ : D.X) (jt : Fin 4 → D.P.L.ι) (hjt : LB.Coh D.P.L (D.Oφ g.pG χ) jt)
    (W' : (Te D I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG χ) jt)
    (ha : W' ≤ (act g).left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG χ) jt) :
    ((act g).left.appLE _ W' ha).hom ((g.t χ).s jt).val =
      ((Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.X (thickObj R I e G) χ) *
      ((snd (Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g.t χ).s jt).val := by sorry
