-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:48.310623+00:00
-- url     : https://prove2.me/theorems/9b7ac65c-6830-4f9d-ace9-0a30eac3e39c
-- title:
--   Pullback Comparison: germ div
-- statement:
--   The Pullback Comparison construction uses the germ div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L160-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L160-L170

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

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_div (M N : LB X) (p p' : (LB.div M N).ι) (y : X)
    (hy : y ∈ (LB.div M N).U p ⊓ (LB.div M N).U p') :
    gU y hy ((LB.div M N).g p p') =
      gU y (⟨hy.1.1, hy.2.1⟩ : y ∈ M.U p.1 ⊓ M.U p'.1) (M.g p.1 p'.1) *
        (gU y (⟨hy.1.2, hy.2.2⟩ : y ∈ N.U p.2 ⊓ N.U p'.2) (N.g p.2 p'.2))⁻¹ := by sorry
