-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_gU_pullAlong_idx
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.gU_pullAlong_idx
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:32:18.317338+00:00
-- url     : https://prove2.me/theorems/ddf7eef2-5aff-5aa2-b7f5-8805d997ad8e
-- title:
--   Cube Pf: g U pull Along idx
-- statement:
--   The Cube Pf construction uses the g U pull Along idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/Transfer.lean#L54-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/Transfer.lean#L54-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr base_eq)

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.gU_pullAlong_idx {X X' Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (jj : K → (L.pull F).ι) (y : Y') (hy : y ∈ LB.wchart (L.pull F) ψ jj)
    (idx : (Y' ⟶ X) → L.ι)
    (mk : ∀ k, y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F))))
    (mem0 : h.base y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F))) :
    gU y hy ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s jj) =
      (∏ k, (gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F))))) ^ (ε k)) *
        Units.map (h.stalkMap y).hom (gU (h.base y) mem0 (t.s (fun k => idx (ψ k ≫ F)))) := by sorry
