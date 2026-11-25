-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_one_sub_mul_geom_54d99a6e3807
-- name    : P2M_GroundTheory_Heights__Theta_SymmFun_one_sub_mul_geom_54d99a6e3807
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:07.490172+00:00
-- url     : https://prove2.me/theorems/256f3245-849c-473c-a25e-c72ecce3b90c
-- title:
--   P2 M Ground Theory Heights  Theta Symm Fun one sub mul geom 54d99a6e3807: P2 M Ground Theory Heights  Theta Symm Fun one sub mul geom 54d99a6e3807
-- statement:
--   The P2 M Ground Theory Heights  Theta Symm Fun one sub mul geom 54d99a6e3807 construction uses the P2 M Ground Theory Heights  Theta Symm Fun one sub mul geom 54d99a6e3807 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Capelli/CompleteHomogeneous.lean#L49-L56

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

theorem P2M_GroundTheory_Heights__Theta_SymmFun_one_sub_mul_geom_54d99a6e3807 (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SymmFun».«one_sub_mul_geom» := P2M_GroundTheory_Heights__Theta_SymmFun_one_sub_mul_geom_54d99a6e3807
