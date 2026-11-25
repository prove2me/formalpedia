-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_eval__formPoly_b2721da1c34e
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_eval__formPoly_b2721da1c34e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:35.67423+00:00
-- url     : https://prove2.me/theorems/c1de88ca-19be-4ae2-b4e4-1c0233cc1343
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points Of Plane eval  form Poly b2721da1c34e: P2 M Ground Theory Heights  Heights Dual Points Of Plane eval  form Poly b2721da1c34e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points Of Plane eval  form Poly b2721da1c34e construction uses the P2 M Ground Theory Heights  Heights Dual Points Of Plane eval  form Poly b2721da1c34e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L45-L48

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

theorem P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_eval__formPoly_b2721da1c34e (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) (v : Fin i → ℂ)
    (p : Σ _ : Unit, T) :
    eval₂Hom σ v (formPoly b p) = dualPlanePt b σ v p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOfPlane».«eval₂_formPoly» := P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_eval__formPoly_b2721da1c34e
