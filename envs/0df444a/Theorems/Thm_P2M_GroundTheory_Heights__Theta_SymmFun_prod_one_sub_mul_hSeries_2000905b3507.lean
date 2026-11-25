-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_prod_one_sub_mul_hSeries_2000905b3507
-- name    : P2M_GroundTheory_Heights__Theta_SymmFun_prod_one_sub_mul_hSeries_2000905b3507
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:49.905583+00:00
-- url     : https://prove2.me/theorems/da8e7b27-c106-5727-95ab-6ccf2685aecb
-- title:
--   P2 M Ground Theory Heights  Theta Symm Fun prod one sub mul h Series 2000905b3507: P2 M Ground Theory Heights  Theta Symm Fun prod one sub mul h Series 2000905b3507
-- statement:
--   The P2 M Ground Theory Heights  Theta Symm Fun prod one sub mul h Series 2000905b3507 construction uses the P2 M Ground Theory Heights  Theta Symm Fun prod one sub mul h Series 2000905b3507 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L58-L61

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

theorem P2M_GroundTheory_Heights__Theta_SymmFun_prod_one_sub_mul_hSeries_2000905b3507 (x : σ → ℂ) :
    (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) * hSeries x = 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SymmFun».«prod_one_sub_mul_hSeries» := P2M_GroundTheory_Heights__Theta_SymmFun_prod_one_sub_mul_hSeries_2000905b3507
