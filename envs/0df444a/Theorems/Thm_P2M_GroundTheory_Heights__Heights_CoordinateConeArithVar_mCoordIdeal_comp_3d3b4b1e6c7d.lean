-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_comp_3d3b4b1e6c7d
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_comp_3d3b4b1e6c7d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:44.096242+00:00
-- url     : https://prove2.me/theorems/4dcd05e7-d305-47e9-8fed-ba55ccd752d3
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal comp 3d3b4b1e6c7d: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal comp 3d3b4b1e6c7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal comp 3d3b4b1e6c7d construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Coord Ideal comp 3d3b4b1e6c7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L156-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L156-L165

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

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_comp_3d3b4b1e6c7d {L : Type} [Field L] (σ : L →+* Ω) (z : (Σ k, ι k) → L) :
    mCoordIdeal (fun p ↦ σ (z p)) = mCoordIdeal z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«mCoordIdeal_comp» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_comp_3d3b4b1e6c7d
