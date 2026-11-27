-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_cartanHomeomorph_apply_2cea746d6a8b
-- name    : P2M_GroundTheory_Heights__Theta_cartanHomeomorph_apply_2cea746d6a8b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:56.536802+00:00
-- url     : https://prove2.me/theorems/a890e5fa-b32d-4897-9ee9-816167416d36
-- title:
--   P2 M Ground Theory Heights  Theta cartan Homeomorph apply 2cea746d6a8b: P2 M Ground Theory Heights  Theta cartan Homeomorph apply 2cea746d6a8b
-- statement:
--   The P2 M Ground Theory Heights  Theta cartan Homeomorph apply 2cea746d6a8b construction uses the P2 M Ground Theory Heights  Theta cartan Homeomorph apply 2cea746d6a8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L154-L156

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

theorem P2M_GroundTheory_Heights__Theta_cartanHomeomorph_apply_2cea746d6a8b (ks : maxCompact G × cartanPos p q) :
    ((cartanHomeomorph ks : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«cartanHomeomorph_apply» := P2M_GroundTheory_Heights__Theta_cartanHomeomorph_apply_2cea746d6a8b
