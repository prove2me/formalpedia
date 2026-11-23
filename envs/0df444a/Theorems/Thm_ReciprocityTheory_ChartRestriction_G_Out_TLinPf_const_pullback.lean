-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_const_pullback
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.const_pullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:37.425467+00:00
-- url     : https://prove2.me/theorems/77ef48c7-0212-40d8-8290-9d47116103f3
-- title:
--   TLin Pf: const pullback
-- statement:
--   The TLin Pf construction uses the const pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ConstPullback.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ConstPullback.lean#L103-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.const_pullback (hGF : GlobalFnsSt) {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (v : Γ(((Over.pullback φ).obj A).left, ⊤)) :
    ∃ κ : Γ(S', ⊤), ((Over.pullback φ).obj A).hom.appTop.hom κ = v := by sorry
