-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_sum_esymm_mul_hsymm_065e66db55c6
-- name    : P2M_GroundTheory_Heights__Theta_SymmFun_sum_esymm_mul_hsymm_065e66db55c6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:54.754861+00:00
-- url     : https://prove2.me/theorems/fb7bd2f2-b762-55a7-9717-a1b6631c7cde
-- title:
--   P2 M Ground Theory Heights  Theta Symm Fun sum esymm mul hsymm 065e66db55c6: P2 M Ground Theory Heights  Theta Symm Fun sum esymm mul hsymm 065e66db55c6
-- statement:
--   The P2 M Ground Theory Heights  Theta Symm Fun sum esymm mul hsymm 065e66db55c6 construction uses the P2 M Ground Theory Heights  Theta Symm Fun sum esymm mul hsymm 065e66db55c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L94-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.SymmFun
open MvPolynomial Finset
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Theta_SymmFun_sum_esymm_mul_hsymm_065e66db55c6 (x : σ → ℂ) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1), (-1) ^ s * eval x (esymm σ ℂ s) * eval x (hsymm σ ℂ (m - s)) =
      if m = 0 then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SymmFun».«sum_esymm_mul_hsymm» := P2M_GroundTheory_Heights__Theta_SymmFun_sum_esymm_mul_hsymm_065e66db55c6
