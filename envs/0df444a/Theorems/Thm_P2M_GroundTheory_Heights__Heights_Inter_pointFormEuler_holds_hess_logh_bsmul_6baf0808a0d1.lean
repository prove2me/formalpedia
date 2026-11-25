-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_logh_bsmul_6baf0808a0d1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_logh_bsmul_6baf0808a0d1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:58.381688+00:00
-- url     : https://prove2.me/theorems/15e59062-829d-5d7e-bb26-7b64fde785d1
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess logh bsmul 6baf0808a0d1: P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess logh bsmul 6baf0808a0d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess logh bsmul 6baf0808a0d1 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess logh bsmul 6baf0808a0d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L117-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L117-L137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_logh_bsmul_6baf0808a0d1 (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) z w (bsmul d z) =
      -fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«hess_logh_bsmul» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_logh_bsmul_6baf0808a0d1
