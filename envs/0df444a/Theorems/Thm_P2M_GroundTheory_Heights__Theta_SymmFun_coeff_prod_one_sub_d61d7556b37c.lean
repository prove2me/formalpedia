-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_coeff_prod_one_sub_d61d7556b37c
-- name    : P2M_GroundTheory_Heights__Theta_SymmFun_coeff_prod_one_sub_d61d7556b37c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:57.348092+00:00
-- url     : https://prove2.me/theorems/b86ea374-da91-4f29-9d84-86489c01cca7
-- title:
--   P2 M Ground Theory Heights  Theta Symm Fun coeff prod one sub d61d7556b37c: P2 M Ground Theory Heights  Theta Symm Fun coeff prod one sub d61d7556b37c
-- statement:
--   The P2 M Ground Theory Heights  Theta Symm Fun coeff prod one sub d61d7556b37c construction uses the P2 M Ground Theory Heights  Theta Symm Fun coeff prod one sub d61d7556b37c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L63-L80

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

theorem P2M_GroundTheory_Heights__Theta_SymmFun_coeff_prod_one_sub_d61d7556b37c (x : σ → ℂ) (s : ℕ) :
    PowerSeries.coeff s (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) =
      (-1) ^ s * eval x (esymm σ ℂ s) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SymmFun».«coeff_prod_one_sub» := P2M_GroundTheory_Heights__Theta_SymmFun_coeff_prod_one_sub_d61d7556b37c
