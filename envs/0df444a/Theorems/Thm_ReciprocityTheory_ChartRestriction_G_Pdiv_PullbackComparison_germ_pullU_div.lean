-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pullU_div
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pullU_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:22.766855+00:00
-- url     : https://prove2.me/theorems/cc8f6fb7-c33c-51d7-b957-e9bc87af503f
-- title:
--   Pullback Comparison: germ pull U div
-- statement:
--   The Pullback Comparison construction uses the germ pull U div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L172-L184

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

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pullU_div (M N : LB X) (a : Y ⟶ X) (p p' : (LB.div M N).ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.div M N).U p ⊓ (LB.div M N).U p'))
    (h1 : y ∈ a ⁻¹ᵁ (M.U p.1 ⊓ M.U p'.1)) (h2 : y ∈ a ⁻¹ᵁ (N.U p.2 ⊓ N.U p'.2)) :
    gU y hy (pullU a _ ((LB.div M N).g p p')) =
      gU y h1 (pullU a _ (M.g p.1 p'.1)) * (gU y h2 (pullU a _ (N.g p.2 p'.2)))⁻¹ := by sorry
