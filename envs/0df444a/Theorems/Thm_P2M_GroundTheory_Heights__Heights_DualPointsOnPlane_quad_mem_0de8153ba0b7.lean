-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_quad_mem_0de8153ba0b7
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_quad_mem_0de8153ba0b7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:35.629805+00:00
-- url     : https://prove2.me/theorems/2437ada0-3cfd-4b95-b631-7afdea896dcf
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points On Plane quad mem 0de8153ba0b7: P2 M Ground Theory Heights  Heights Dual Points On Plane quad mem 0de8153ba0b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points On Plane quad mem 0de8153ba0b7 construction uses the P2 M Ground Theory Heights  Heights Dual Points On Plane quad mem 0de8153ba0b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L70-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L70-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_quad_mem_0de8153ba0b7 (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) :
    quad b α s r ∈ dualIdeal b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOnPlane».«quad_mem» := P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_quad_mem_0de8153ba0b7
