-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_horizontal_871a820b28bd
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_horizontal_871a820b28bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:03.590836+00:00
-- url     : https://prove2.me/theorems/2273f031-c228-46ef-8465-144414c356ed
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var horizontal 871a820b28bd: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var horizontal 871a820b28bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var horizontal 871a820b28bd construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var horizontal 871a820b28bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L88-L93

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

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_horizontal_871a820b28bd [CharZero Ω] (y : (Σ k, ι k) → Ω) : IsHorizontal (mCoordIdeal y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«horizontal» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_horizontal_871a820b28bd
