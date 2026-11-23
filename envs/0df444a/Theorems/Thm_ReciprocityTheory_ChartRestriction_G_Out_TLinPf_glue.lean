-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_glue
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:28.936152+00:00
-- url     : https://prove2.me/theorems/4af34258-02d6-4710-8778-7c7af86f8b77
-- title:
--   TLin Pf: glue
-- statement:
--   The TLin Pf construction uses the glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ConstPullback.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ConstPullback.lean#L18-L24

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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.glue {Y : Scheme.{0}} {κ : Type} (U : κ → Y.Opens) (hc : ⨆ j, U j = ⊤)
    (f : ∀ j, Γ(Y, U j))
    (h : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (f i) =
      (Y.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (f j)) :
    ∃ s : Γ(Y, ⊤), ∀ j, (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom s = f j := by sorry
