-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inr_48e68431394d
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inr_48e68431394d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:58.438361+00:00
-- url     : https://prove2.me/theorems/44d41346-8a37-556b-9fb4-d3ab4e6caa08
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inr 48e68431394d: P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inr 48e68431394d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inr 48e68431394d construction uses the P2 M Ground Theory Heights  Heights Chart Kernel chart Subst inr 48e68431394d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L175-L178

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inr_48e68431394d (g : MvPolynomial (Fin e × Fin n) F) :
    chartSubst I t e (rename Sum.inr g) =
      map (chartX I t e) (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«chartSubst_inr» := P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inr_48e68431394d
