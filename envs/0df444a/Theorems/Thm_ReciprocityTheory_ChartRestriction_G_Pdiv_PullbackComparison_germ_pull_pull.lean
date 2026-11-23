-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull_pull
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pull_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:44.884802+00:00
-- url     : https://prove2.me/theorems/b54d0953-2d98-4dec-b10f-4cd35608b81a
-- title:
--   Pullback Comparison: germ pull pull
-- statement:
--   The Pullback Comparison construction uses the germ pull pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L125-L132

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

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pull_pull (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (i j : PUnit.{1} → PUnit.{1} → L.ι) (y : Z)
    (hy : y ∈ ((L.pull a).pull b).U i ⊓ ((L.pull a).pull b).U j)
    (hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))) :
    gU y hy (((L.pull a).pull b).g i j) =
      gU y hy' (pullU (b ≫ a) _ (L.g (i PUnit.unit PUnit.unit) (j PUnit.unit PUnit.unit))) := by sorry
