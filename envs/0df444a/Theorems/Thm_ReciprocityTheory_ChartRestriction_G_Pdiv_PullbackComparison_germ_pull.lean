-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:02.660906+00:00
-- url     : https://prove2.me/theorems/1169a0bd-186a-4448-8d0e-1c897174bbf4
-- title:
--   Pullback Comparison: germ pull
-- statement:
--   The Pullback Comparison construction uses the germ pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L101-L106

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

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pull (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) (y : Y)
    (hy : y ∈ (L.pull a).U i ⊓ (L.pull a).U j)
    (hy' : y ∈ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))) :
    gU y hy ((L.pull a).g i j) = gU y hy' (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := by sorry
