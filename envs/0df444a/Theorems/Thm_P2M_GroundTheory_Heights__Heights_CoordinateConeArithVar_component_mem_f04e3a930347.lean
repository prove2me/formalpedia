-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_component_mem_f04e3a930347
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_component_mem_f04e3a930347
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:39.376593+00:00
-- url     : https://prove2.me/theorems/6561c49b-15dc-507d-973a-1fb19c1aa387
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var component mem f04e3a930347: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var component mem f04e3a930347
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var component mem f04e3a930347 construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var component mem f04e3a930347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L46-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L46-L71

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_component_mem_f04e3a930347 [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : MRing ι)
    (hf : f ∈ mCoordIdeal y) (m : K → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) m f ∈ mCoordIdeal y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«component_mem» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_component_mem_f04e3a930347
