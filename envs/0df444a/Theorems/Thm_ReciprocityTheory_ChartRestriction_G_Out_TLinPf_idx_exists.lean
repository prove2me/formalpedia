-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_idx_exists
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.idx_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:25.075803+00:00
-- url     : https://prove2.me/theorems/d88d23e4-23e8-4b96-a6e4-f56b0ff0112f
-- title:
--   TLin Pf: idx exists
-- statement:
--   The TLin Pf construction uses the idx exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ConstPullback.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ConstPullback.lean#L79-L82

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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.idx_exists {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Y) :
    ∃ idx : (Y ⟶ X) → L.ι, ∀ ψ, ψ.base y ∈ L.U (idx ψ) := by sorry
