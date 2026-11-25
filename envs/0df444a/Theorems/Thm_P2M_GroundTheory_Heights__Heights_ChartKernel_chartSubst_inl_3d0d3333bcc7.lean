-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inl_3d0d3333bcc7
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inl_3d0d3333bcc7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:51.729025+00:00
-- url     : https://prove2.me/theorems/a5fc103d-b91c-49da-8b84-2750f6d2c2bb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inl 3d0d3333bcc7: P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inl 3d0d3333bcc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inl 3d0d3333bcc7 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inl 3d0d3333bcc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L165-L173

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inl_3d0d3333bcc7 (g : MvPolynomial (Fin n) F) :
    chartSubst I t e (rename Sum.inl g) = C (chartX I t e g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«chartSubst_inl» := P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inl_3d0d3333bcc7
