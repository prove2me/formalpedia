-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_comp_holo_7a1539b9bd8f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_comp_holo_7a1539b9bd8f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:51.165783+00:00
-- url     : https://prove2.me/theorems/eaf8801c-bbdb-5c9a-89f3-a03bde321b94
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess comp holo 7a1539b9bd8f: P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess comp holo 7a1539b9bd8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess comp holo 7a1539b9bd8f construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds hess comp holo 7a1539b9bd8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L145-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L145-L177

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_comp_holo_7a1539b9bd8f {φ : ((Σ k, ι k) → ℂ) → ℝ} {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F y)) (hF : AnalyticAt ℂ F y) (u v : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fderiv ℝ φ) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ φ (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«hess_comp_holo» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_comp_holo_7a1539b9bd8f
