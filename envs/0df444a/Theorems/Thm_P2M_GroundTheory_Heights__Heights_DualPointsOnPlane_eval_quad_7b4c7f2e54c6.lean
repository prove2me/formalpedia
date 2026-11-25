-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_eval_quad_7b4c7f2e54c6
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_eval_quad_7b4c7f2e54c6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:56.486291+00:00
-- url     : https://prove2.me/theorems/3e096844-a0f8-4e70-a6af-71f1892632ee
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points On Plane eval quad 7b4c7f2e54c6: P2 M Ground Theory Heights  Heights Dual Points On Plane eval quad 7b4c7f2e54c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points On Plane eval quad 7b4c7f2e54c6 construction uses the P2 M Ground Theory Heights  Heights Dual Points On Plane eval quad 7b4c7f2e54c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L102-L106

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

theorem P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_eval_quad_7b4c7f2e54c6 (z : (Σ _ : Unit, T) → ℂ) (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K)
    (s r : T) : eval z (map (Int.castRingHom ℂ) (quad b α s r)) =
      z ⟨(), s⟩ * ∑ t, (mulMat b α r t : ℂ) * z ⟨(), t⟩ -
        (∑ t, (mulMat b α s t : ℂ) * z ⟨(), t⟩) * z ⟨(), r⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOnPlane».«eval_quad» := P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_eval_quad_7b4c7f2e54c6
