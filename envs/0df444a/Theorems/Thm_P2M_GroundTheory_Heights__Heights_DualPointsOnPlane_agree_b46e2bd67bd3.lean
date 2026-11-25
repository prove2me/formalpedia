-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_agree_b46e2bd67bd3
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_agree_b46e2bd67bd3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:34.425088+00:00
-- url     : https://prove2.me/theorems/d8c11c37-7d2f-58d4-8cc9-bb87e3d6fa0d
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points On Plane agree b46e2bd67bd3: P2 M Ground Theory Heights  Heights Dual Points On Plane agree b46e2bd67bd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points On Plane agree b46e2bd67bd3 construction uses the P2 M Ground Theory Heights  Heights Dual Points On Plane agree b46e2bd67bd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L108-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L108-L143

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

theorem P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_agree_b46e2bd67bd3 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : z ∈ mcPts (dualIdeal b)) (α : 𝓞 K) (p q : (K →+* ℂ) × Fin i)
    (hp : dualRecover b hb (fun t => z ⟨(), t⟩) p ≠ 0) (hq : dualRecover b hb (fun t => z ⟨(), t⟩) q ≠ 0) :
    p.1 α = q.1 α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOnPlane».«agree» := P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_agree_b46e2bd67bd3
