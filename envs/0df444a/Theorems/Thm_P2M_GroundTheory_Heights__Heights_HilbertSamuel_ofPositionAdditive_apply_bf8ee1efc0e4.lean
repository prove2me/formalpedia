-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ofPositionAdditive_apply_bf8ee1efc0e4
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ofPositionAdditive_apply_bf8ee1efc0e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:48.364033+00:00
-- url     : https://prove2.me/theorems/84059ec6-5ae2-5718-9f90-5c9ed66b42b1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel of Position Additive apply bf8ee1efc0e4: P2 M Ground Theory Heights  Heights Hilbert Samuel of Position Additive apply bf8ee1efc0e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel of Position Additive apply bf8ee1efc0e4 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel of Position Additive apply bf8ee1efc0e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L131-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ofPositionAdditive_apply_bf8ee1efc0e4 {n : ℕ} (L : (Fin n → K → ℤ) → ℤ) (hadd) (m : Fin n → K → ℤ) :
    ofPositionAdditive L hadd m = L m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ofPositionAdditive_apply» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ofPositionAdditive_apply_bf8ee1efc0e4
