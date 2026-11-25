-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_genSubst_scale_558405ff26bb
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_genSubst_scale_558405ff26bb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:34.169861+00:00
-- url     : https://prove2.me/theorems/4723c370-4d9c-432b-81c8-0db25b7f0369
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel gen Subst scale 558405ff26bb: P2 M Ground Theory Heights  Heights Chart Kernel gen Subst scale 558405ff26bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel gen Subst scale 558405ff26bb construction uses the P2 M Ground Theory Heights  Heights Chart Kernel gen Subst scale 558405ff26bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L134-L139

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_genSubst_scale_558405ff26bb {K : Type*} [Field K] {e : ℕ} (ξ s : Fin n → K) (τ : K) (ij : Fin e × Fin n) :
    genSubst ξ (fun m => τ⁻¹ * s m) ij = genSubst (τ⁻¹ • ξ) s ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«genSubst_scale» := P2M_GroundTheory_Heights__Heights_ChartKernel_genSubst_scale_558405ff26bb
