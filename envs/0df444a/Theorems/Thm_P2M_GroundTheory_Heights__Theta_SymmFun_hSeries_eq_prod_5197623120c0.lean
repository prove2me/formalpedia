-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_hSeries_eq_prod_5197623120c0
-- name    : P2M_GroundTheory_Heights__Theta_SymmFun_hSeries_eq_prod_5197623120c0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:44.133481+00:00
-- url     : https://prove2.me/theorems/9459fe2d-352d-52ce-a887-0fc70b9107de
-- title:
--   P2 M Ground Theory Heights  Theta Symm Fun h Series eq prod 5197623120c0: P2 M Ground Theory Heights  Theta Symm Fun h Series eq prod 5197623120c0
-- statement:
--   The P2 M Ground Theory Heights  Theta Symm Fun h Series eq prod 5197623120c0 construction uses the P2 M Ground Theory Heights  Theta Symm Fun h Series eq prod 5197623120c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L43-L47

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

theorem P2M_GroundTheory_Heights__Theta_SymmFun_hSeries_eq_prod_5197623120c0 (x : σ → ℂ) :
    hSeries x = ∏ i, PowerSeries.mk fun k => x i ^ k := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SymmFun».«hSeries_eq_prod» := P2M_GroundTheory_Heights__Theta_SymmFun_hSeries_eq_prod_5197623120c0
