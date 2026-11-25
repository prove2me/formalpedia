-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_map_genSubst_X_a8867dcefebe
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_map_genSubst_X_a8867dcefebe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:13.6258+00:00
-- url     : https://prove2.me/theorems/1fe39aa7-23a6-4e5f-a92e-f9d77934007d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel map gen Subst X a8867dcefebe: P2 M Ground Theory Heights  Heights Chart Kernel map gen Subst X a8867dcefebe
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel map gen Subst X a8867dcefebe construction uses the P2 M Ground Theory Heights  Heights Chart Kernel map gen Subst X a8867dcefebe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L116-L120

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_map_genSubst_X_a8867dcefebe {B : Type*} [CommRing B] {e : ℕ} (q : MvPolynomial (Fin n) F →+* B) (t : Fin n → F)
    (ij : Fin e × Fin n) :
    map q (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m)) ij) =
      genSubst (fun m => q (X m)) (fun m => q (C (t m))) ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«map_genSubst_X» := P2M_GroundTheory_Heights__Heights_ChartKernel_map_genSubst_X_a8867dcefebe
