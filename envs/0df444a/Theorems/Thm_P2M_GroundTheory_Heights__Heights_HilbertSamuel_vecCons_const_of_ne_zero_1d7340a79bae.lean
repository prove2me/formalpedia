-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_vecCons_const_of_ne_zero_1d7340a79bae
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_vecCons_const_of_ne_zero_1d7340a79bae
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:41.018192+00:00
-- url     : https://prove2.me/theorems/89d71c10-7f0b-5fe3-879a-2e6a0ef90015
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel vec Cons const of ne zero 1d7340a79bae: P2 M Ground Theory Heights  Heights Hilbert Samuel vec Cons const of ne zero 1d7340a79bae
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel vec Cons const of ne zero 1d7340a79bae construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel vec Cons const of ne zero 1d7340a79bae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L136-L139

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_vecCons_const_of_ne_zero_1d7340a79bae {d : ℕ} (y x : K → ℤ) (k : Fin (d + 1)) (hk : k ≠ 0) :
    Matrix.vecCons y (fun _ : Fin d => x) k = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«vecCons_const_of_ne_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_vecCons_const_of_ne_zero_1d7340a79bae
