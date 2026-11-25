-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_analytic_log_14266ed031aa
-- name    : P2M_GroundTheory_Heights__Heights_Regular_exists_analytic_log_14266ed031aa
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:06.870997+00:00
-- url     : https://prove2.me/theorems/65a70d1c-6b7d-4269-9fe2-7bf0ab63103b
-- title:
--   P2 M Ground Theory Heights  Heights Regular exists analytic log 14266ed031aa: P2 M Ground Theory Heights  Heights Regular exists analytic log 14266ed031aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular exists analytic log 14266ed031aa construction uses the P2 M Ground Theory Heights  Heights Regular exists analytic log 14266ed031aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L52-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L52-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_exists_analytic_log_14266ed031aa {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (hU : IsOpen U) (hc : Convex ℝ U) (hne : U.Nonempty) {h : E → ℂ} (hh : AnalyticOnNhd ℂ h U)
    (h0 : ∀ z ∈ U, h z ≠ 0) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G U ∧ ∀ z ∈ U, Complex.exp (G z) = h z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«exists_analytic_log» := P2M_GroundTheory_Heights__Heights_Regular_exists_analytic_log_14266ed031aa
