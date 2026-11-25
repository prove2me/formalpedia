-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_scaleT_inv_cd75bf8c9ee9
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_scaleT_inv_cd75bf8c9ee9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:35.366991+00:00
-- url     : https://prove2.me/theorems/f0dd5b10-242a-4442-9327-520821ea4b5d
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var scale T inv cd75bf8c9ee9: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var scale T inv cd75bf8c9ee9
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var scale T inv cd75bf8c9ee9 construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var scale T inv cd75bf8c9ee9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L115-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_scaleT_inv_cd75bf8c9ee9 (a : K → Ω) (ha : ∀ k, a k ≠ 0) (g : MvPolynomial K Ω) :
    scaleT (fun k ↦ (a k)⁻¹) (scaleT a g) = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«scaleT_inv» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_scaleT_inv_cd75bf8c9ee9
