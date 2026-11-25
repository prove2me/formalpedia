-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_smul_of_isHomogeneous_28aad74d1df1
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_smul_of_isHomogeneous_28aad74d1df1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:09.577471+00:00
-- url     : https://prove2.me/theorems/fd397d73-26ef-42cc-8585-13e74cb9ac02
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel aeval smul of is Homogeneous 28aad74d1df1: P2 M Ground Theory Heights  Heights Chart Kernel aeval smul of is Homogeneous 28aad74d1df1
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel aeval smul of is Homogeneous 28aad74d1df1 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel aeval smul of is Homogeneous 28aad74d1df1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L13-L22

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_smul_of_isHomogeneous_28aad74d1df1 {F σ S : Type*} [Field F] [CommRing S] [Algebra F S]
    {φ : MvPolynomial σ F} {d : ℕ} (hφ : φ.IsHomogeneous d) (a : S) (x : σ → S) :
    aeval (a • x) φ = a ^ d * aeval x φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«aeval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_smul_of_isHomogeneous_28aad74d1df1
