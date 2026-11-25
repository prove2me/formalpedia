-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_1015ab595432
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_1015ab595432
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:20.932789+00:00
-- url     : https://prove2.me/theorems/f9a20791-500f-5619-a53b-30022594cac2
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj 1015ab595432: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj 1015ab595432
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj 1015ab595432 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj 1015ab595432 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L172-L177

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
omit hH ha

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_1015ab595432 {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hga : g *ᵥ a = a) (y : ι → ℂ)
    (s : ℂ) : g * heisMat H a y s = heisMat H a (g *ᵥ y) s * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_conj» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_1015ab595432
