-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartIncIdeal_le_ker_044de4c79fd0
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_chartIncIdeal_le_ker_044de4c79fd0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:51.60697+00:00
-- url     : https://prove2.me/theorems/fd455664-397b-5291-8ca3-d59b8a48f259
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel chart Inc Ideal le ker 044de4c79fd0: P2 M Ground Theory Heights  Heights Chart Kernel chart Inc Ideal le ker 044de4c79fd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel chart Inc Ideal le ker 044de4c79fd0 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel chart Inc Ideal le ker 044de4c79fd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L184-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L184-L202

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_chartIncIdeal_le_ker_044de4c79fd0 : chartIncIdeal I t e ≤ RingHom.ker (chartSubst I t e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«chartIncIdeal_le_ker» := P2M_GroundTheory_Heights__Heights_ChartKernel_chartIncIdeal_le_ker_044de4c79fd0
