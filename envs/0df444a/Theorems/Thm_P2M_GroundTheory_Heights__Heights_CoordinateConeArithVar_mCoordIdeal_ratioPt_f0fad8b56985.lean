-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPt_f0fad8b56985
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPt_f0fad8b56985
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:04.758748+00:00
-- url     : https://prove2.me/theorems/1faa41d9-b0eb-4216-bc29-f8a78d76be03
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal ratio Pt f0fad8b56985: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal ratio Pt f0fad8b56985
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal ratio Pt f0fad8b56985 construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal ratio Pt f0fad8b56985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L142-L152

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPt_f0fad8b56985 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    mCoordIdeal y = mCoordIdeal (ratioPt y c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«mCoordIdeal_ratioPt» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPt_f0fad8b56985
