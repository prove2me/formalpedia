-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_pullGen_pullAlong
-- name    : ReciprocityTheory.ChartRestriction.G.Out.LBxP.pullGen_pullAlong
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:44.300141+00:00
-- url     : https://prove2.me/theorems/12fe53a5-7faf-5646-a11c-bd05c9f1ee8a
-- title:
--   LBx P: pull Gen pull Along
-- statement:
--   The LBx P construction uses the pull Gen pull Along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/GeneratorPullback/PullAlong.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/GeneratorPullback/PullAlong.lean#L53-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.LBxP
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res')
variable {X X' Y Y' Z Z' : Scheme.{0}}
variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Out.LBxP.pullGen_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε))
    (a : Z ⟶ Y') (h2 : Z ⟶ Z') (b : Z' ⟶ Y) (hab : a ≫ h = h2 ≫ b)
    (hψ2 : ∀ k, (a ≫ ψ k) ≫ F = h2 ≫ (b ≫ φ k)) :
    LB.pullGen (L.pull F) ψ ε (GeneratorPullback.pullAlong L F h φ ε ψ hψ t) a =
      GeneratorPullback.pullAlong L F h2 (fun k => b ≫ φ k) ε (fun k => a ≫ ψ k) hψ2 (LB.pullGen L φ ε t b) := by sorry
