-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_recover_cd4a48f275be
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_recover_cd4a48f275be
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:17.159172+00:00
-- url     : https://prove2.me/theorems/617df17d-8528-4a14-9300-251ce69e9e0b
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat recover cd4a48f275be: P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat recover cd4a48f275be
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat recover cd4a48f275be construction uses the P2 M Ground Theory Heights  Heights Dual Points On Plane mul Mat recover cd4a48f275be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean#L44-L65

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

theorem P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_recover_cd4a48f275be (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (α : 𝓞 K) (Z : T → ℂ) (s : T) :
    ∑ t, (mulMat b α s t : ℂ) * Z t =
      ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (p.1 α * dualRecover b hb Z p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOnPlane».«mulMat_recover» := P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_recover_cd4a48f275be
