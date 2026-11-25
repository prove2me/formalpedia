-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_coe_cartanMul_bf808fc8f3c9
-- name    : P2M_GroundTheory_Heights__Theta_coe_cartanMul_bf808fc8f3c9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:26.454742+00:00
-- url     : https://prove2.me/theorems/7547eca1-3f89-54e5-95b9-0be2c3b44dd0
-- title:
--   P2 M Ground Theory Heights  Theta coe cartan Mul bf808fc8f3c9: P2 M Ground Theory Heights  Theta coe cartan Mul bf808fc8f3c9
-- statement:
--   The P2 M Ground Theory Heights  Theta coe cartan Mul bf808fc8f3c9 construction uses the P2 M Ground Theory Heights  Theta coe cartan Mul bf808fc8f3c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L122-L124

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
local notation "G" => indefiniteUnitaryGroup p q

theorem P2M_GroundTheory_Heights__Theta_coe_cartanMul_bf808fc8f3c9 (ks : maxCompact G × cartanPos p q) :
    ((cartanMul ks : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«coe_cartanMul» := P2M_GroundTheory_Heights__Theta_coe_cartanMul_bf808fc8f3c9
