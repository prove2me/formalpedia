-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartEv_chartSubst_0bbd94b367c7
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_chartEv_chartSubst_0bbd94b367c7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:26.318562+00:00
-- url     : https://prove2.me/theorems/80505068-4caa-4399-811b-29900c622148
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel chart Ev chart Subst 0bbd94b367c7: P2 M Ground Theory Heights  Heights Chart Kernel chart Ev chart Subst 0bbd94b367c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel chart Ev chart Subst 0bbd94b367c7 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel chart Ev chart Subst 0bbd94b367c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L204-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L204-L234

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_chartEv_chartSubst_0bbd94b367c7 (p : MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :
    chartEv I t e (chartSubst I t e p) = Ideal.Quotient.mk (chartIncIdeal I t e) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«chartEv_chartSubst» := P2M_GroundTheory_Heights__Heights_ChartKernel_chartEv_chartSubst_0bbd94b367c7
