-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genSubst_scale_287273e9ddd5
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genSubst_scale_287273e9ddd5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:52.367973+00:00
-- url     : https://prove2.me/theorems/3f93c318-9b02-5f70-b5de-486a7d2e511c
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Subst scale 287273e9ddd5: P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Subst scale 287273e9ddd5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Subst scale 287273e9ddd5 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel aeval gen Subst scale 287273e9ddd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L141-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L141-L153

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genSubst_scale_287273e9ddd5 {K : Type*} [Field K] [Algebra F K] {e : ℕ} (ξ : Fin n → K) (τ : K) (t : Fin n → F)
    (g : MvPolynomial (Fin e × Fin n) F) :
    aeval (genSubst ξ (fun m => τ⁻¹ * algebraMap F K (t m))) g =
      map (aeval (τ⁻¹ • ξ)).toRingHom
        (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«aeval_genSubst_scale» := P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genSubst_scale_287273e9ddd5
