-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_of_exp_eq_f1c35840ad06
-- name    : P2M_GroundTheory_Heights__Heights_Regular_analyticAt_of_exp_eq_f1c35840ad06
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:39.071947+00:00
-- url     : https://prove2.me/theorems/98d121be-37bf-4a84-8e7d-b44e6a277f1b
-- title:
--   P2 M Ground Theory Heights  Heights Regular analytic At of exp eq f1c35840ad06: P2 M Ground Theory Heights  Heights Regular analytic At of exp eq f1c35840ad06
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular analytic At of exp eq f1c35840ad06 construction uses the P2 M Ground Theory Heights  Heights Regular analytic At of exp eq f1c35840ad06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L11-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L11-L50

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

theorem P2M_GroundTheory_Heights__Heights_Regular_analyticAt_of_exp_eq_f1c35840ad06 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g h : E → ℂ}
    {z₀ : E} (hg : ContinuousAt g z₀) (hh : AnalyticAt ℂ h z₀)
    (he : ∀ᶠ z in 𝓝 z₀, Complex.exp (g z) = h z) : AnalyticAt ℂ g z₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«analyticAt_of_exp_eq» := P2M_GroundTheory_Heights__Heights_Regular_analyticAt_of_exp_eq_f1c35840ad06
