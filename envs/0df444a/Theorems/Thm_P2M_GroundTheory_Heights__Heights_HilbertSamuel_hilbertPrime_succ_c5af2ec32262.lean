-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_hilbertPrime_succ_c5af2ec32262
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_hilbertPrime_succ_c5af2ec32262
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:54.305238+00:00
-- url     : https://prove2.me/theorems/867cea5c-3e15-4df7-b081-e19b055fed51
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel hilbert Prime succ c5af2ec32262: P2 M Ground Theory Heights  Heights Hilbert Samuel hilbert Prime succ c5af2ec32262
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel hilbert Prime succ c5af2ec32262 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel hilbert Prime succ c5af2ec32262 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L271-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L271-L397

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_hilbertPrime_succ_c5af2ec32262 (d : ℕ) (hM : MixedNumberPolynomial.Statement.{u})
    (hI : HilbertIncrement.Statement.{u}) (hmod : HilbertModule.AtDim.{u, u} d) :
    HilbertPrime.AtDim.{u} (d + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«hilbertPrime_succ» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_hilbertPrime_succ_c5af2ec32262
