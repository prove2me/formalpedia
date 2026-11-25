-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_eval_hsymm_04c692b73247
-- name    : P2M_GroundTheory_Heights__Theta_SymmFun_eval_hsymm_04c692b73247
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:55.006402+00:00
-- url     : https://prove2.me/theorems/c16a826e-187d-4441-bcae-e8d694576dc9
-- title:
--   P2 M Ground Theory Heights  Theta Symm Fun eval hsymm 04c692b73247: P2 M Ground Theory Heights  Theta Symm Fun eval hsymm 04c692b73247
-- statement:
--   The P2 M Ground Theory Heights  Theta Symm Fun eval hsymm 04c692b73247 construction uses the P2 M Ground Theory Heights  Theta Symm Fun eval hsymm 04c692b73247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L12-L39

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

theorem P2M_GroundTheory_Heights__Theta_SymmFun_eval_hsymm_04c692b73247 (x : σ → ℂ) (b : ℕ) :
    eval x (hsymm σ ℂ b) = ∑ l ∈ finsuppAntidiag (univ : Finset σ) b, ∏ i, x i ^ l i := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SymmFun».«eval_hsymm» := P2M_GroundTheory_Heights__Theta_SymmFun_eval_hsymm_04c692b73247
