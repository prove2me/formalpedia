-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mul_0b194300fa17
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mul_0b194300fa17
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:37.826597+00:00
-- url     : https://prove2.me/theorems/2351d472-0e63-44b5-b4a6-f00a02a33f36
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul 0b194300fa17: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul 0b194300fa17
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul 0b194300fa17 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul 0b194300fa17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L150-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mul_0b194300fa17 {y₁ y₂ : ι → ℂ} (h₁ : hForm H a y₁ = 0) (h₂ : hForm H a y₂ = 0)
    (s₁ s₂ : ℂ) :
    heisMat H a y₁ s₁ * heisMat H a y₂ s₂ =
      heisMat H a (y₁ + y₂) (s₁ + s₂ - hForm H y₁ y₂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mul_0b194300fa17
