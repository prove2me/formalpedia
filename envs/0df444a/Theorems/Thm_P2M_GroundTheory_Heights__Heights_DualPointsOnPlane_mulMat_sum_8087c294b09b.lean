-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:52.465065+00:00
-- url     : https://prove2.me/theorems/a3e56e0b-69f8-4c9d-9651-f211c66c70e9
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat sum 8087c294b09b: P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat sum 8087c294b09b
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat sum 8087c294b09b construction uses the P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat sum 8087c294b09b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L26-L32

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

theorem P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s : T) (j : Fin i) :
    ∑ t, (mulMat b α s t : K) * (b t : Fin i → K) j = (α : K) * (b s : Fin i → K) j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOnPlane».«mulMat_sum» := P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b
