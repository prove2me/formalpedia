-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_corr_pullAlong_sameSum
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.corr_pullAlong_sameSum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:54.243569+00:00
-- url     : https://prove2.me/theorems/ebf0deee-90bc-43d3-9565-5c9fe4d9fb53
-- title:
--   Cube Pf: corr pull Along same Sum
-- statement:
--   The Cube Pf construction uses the corr pull Along same Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/Transfer.lean#L84-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/Transfer.lean#L84-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer
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
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.corr_pullAlong_sameSum {X X' Y Y' : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (ψ : K → (Y' ⟶ X')) (ψ' : K' → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (hψ' : ∀ k, ψ' k ≫ F = h ≫ φ' k)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (ht' : t'.IsGen) (hc : LB.Gen.Corr L φ ε φ' ε' t t') (hS : LB.SameSum ψ ε ψ' ε') :
    LB.Gen.Corr (L.pull F) ψ ε ψ' ε' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t)
      (GeneratorPullback.pullAlong L F h φ' ε' ψ' hψ' t') := by sorry
