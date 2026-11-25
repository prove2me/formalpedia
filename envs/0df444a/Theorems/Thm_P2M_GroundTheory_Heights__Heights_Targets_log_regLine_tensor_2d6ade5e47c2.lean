-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_log_regLine_tensor_2d6ade5e47c2
-- name    : P2M_GroundTheory_Heights__Heights_Targets_log_regLine_tensor_2d6ade5e47c2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:30.545796+00:00
-- url     : https://prove2.me/theorems/2c03a572-8758-4c07-b4e5-f887e95e2874
-- title:
--   P2 M Ground Theory Heights  Heights Targets log reg Line tensor 2d6ade5e47c2: P2 M Ground Theory Heights  Heights Targets log reg Line tensor 2d6ade5e47c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets log reg Line tensor 2d6ade5e47c2 construction uses the P2 M Ground Theory Heights  Heights Targets log reg Line tensor 2d6ade5e47c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/LogRegLineTensor.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/LogRegLineTensor.lean#L17-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongSectionLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LogRegLineTensor
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem P2M_GroundTheory_Heights__Heights_Targets_log_regLine_tensor_2d6ade5e47c2 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (s : MRing ι) {ε : ℝ} (hε : 0 < ε) {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : IsMultiHomog s a)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((regLine A s ε ha hs).tensor A).h z) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«log_regLine_tensor» := P2M_GroundTheory_Heights__Heights_Targets_log_regLine_tensor_2d6ade5e47c2
