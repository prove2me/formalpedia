-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:50.394799+00:00
-- url     : https://prove2.me/theorems/e96742eb-07cd-4a57-bcc5-a7e7711e2f86
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat unitary b973147ebfea: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat unitary b973147ebfea
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat unitary b973147ebfea construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat unitary b973147ebfea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L160-L168

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea {y : ι → ℂ} (hy : hForm H a y = 0) {s : ℂ}
    (hs : s + starRingEnd ℂ s + hForm H y y = 0) :
    (heisMat H a y s)ᴴ * H * heisMat H a y s = H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_unitary» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea
