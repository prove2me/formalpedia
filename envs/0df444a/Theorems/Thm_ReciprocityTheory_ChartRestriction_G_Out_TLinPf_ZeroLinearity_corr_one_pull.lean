-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_one_pull
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.corr_one_pull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:40.482569+00:00
-- url     : https://prove2.me/theorems/fc9e4ac2-2b0a-5caa-81ca-92419a09df60
-- title:
--   Zero Linearity: corr one pull
-- statement:
--   The Zero Linearity construction uses the corr one pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L130-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
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
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.corr_one_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (hC : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim t (LB.oneGen L)) (h : Z ⟶ Y) :
    LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L) := by sorry
