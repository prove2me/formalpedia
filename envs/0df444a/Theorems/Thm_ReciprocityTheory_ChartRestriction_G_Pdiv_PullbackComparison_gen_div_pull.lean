-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gen_div_pull
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_div_pull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:20.089254+00:00
-- url     : https://prove2.me/theorems/252ba651-9fa5-47c7-be99-53e03c15e377
-- title:
--   Pullback Comparison: gen div pull
-- statement:
--   The Pullback Comparison construction uses the gen div pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L186-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L186-L225

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_div_pull (L : LB X) (sG : X ⟶ X) (φ₂ : Y ⟶ X) (sA : Y ⟶ Y) (h : sA ≫ φ₂ = φ₂ ≫ sG)
    (hw : ∃ t : LB.Gen ((LB.div (L.pull sG) L).pull φ₂), t.IsGen) :
    ∃ t : LB.Gen (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)), t.IsGen := by sorry
