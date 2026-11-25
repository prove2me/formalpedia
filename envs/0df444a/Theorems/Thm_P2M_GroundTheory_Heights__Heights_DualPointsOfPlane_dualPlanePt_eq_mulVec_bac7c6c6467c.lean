-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_dualPlanePt_eq_mulVec_bac7c6c6467c
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_dualPlanePt_eq_mulVec_bac7c6c6467c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:39.137064+00:00
-- url     : https://prove2.me/theorems/00ce1f95-b749-4f54-b8e5-7896f044fcaf
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points Of Plane dual Plane Pt eq mul Vec bac7c6c6467c: P2 M Ground Theory Heights  Heights Dual Points Of Plane dual Plane Pt eq mul Vec bac7c6c6467c
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points Of Plane dual Plane Pt eq mul Vec bac7c6c6467c construction uses the P2 M Ground Theory Heights  Heights Dual Points Of Plane dual Plane Pt eq mul Vec bac7c6c6467c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L33-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
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
open GroundTheory.Heights₂.Heights.DualPointsOfPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_dualPlanePt_eq_mulVec_bac7c6c6467c [DecidableEq (K →+* ℂ)] (b : Module.Basis T ℤ (dualLattice F))
    (σ : K →+* ℂ) (v : Fin i → ℂ) (t : T) :
    dualPlanePt b σ v ⟨(), t⟩ =
      (dualEmbMatrix b *ᵥ fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOfPlane».«dualPlanePt_eq_mulVec» := P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_dualPlanePt_eq_mulVec_bac7c6c6467c
