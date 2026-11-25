-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_analyticAt_eval_of_analyticAt_zero_79fc8297a2cb
-- name    : P2M_GroundTheory_Heights__Heights_analyticAt_eval_of_analyticAt_zero_79fc8297a2cb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:03.972804+00:00
-- url     : https://prove2.me/theorems/3d71739e-e370-4727-8318-cc6774345a12
-- title:
--   P2 M Ground Theory Heights  Heights analytic At eval of analytic At zero 79fc8297a2cb: P2 M Ground Theory Heights  Heights analytic At eval of analytic At zero 79fc8297a2cb
-- statement:
--   The P2 M Ground Theory Heights  Heights analytic At eval of analytic At zero 79fc8297a2cb construction uses the P2 M Ground Theory Heights  Heights analytic At eval of analytic At zero 79fc8297a2cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L22-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrdersLiftCentre
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
open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem P2M_GroundTheory_Heights__Heights_analyticAt_eval_of_analyticAt_zero_79fc8297a2cb {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«analyticAt_eval_of_analyticAt_zero» := P2M_GroundTheory_Heights__Heights_analyticAt_eval_of_analyticAt_zero_79fc8297a2cb
