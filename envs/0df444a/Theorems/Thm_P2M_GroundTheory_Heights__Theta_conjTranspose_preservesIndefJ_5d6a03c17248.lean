-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_conjTranspose_preservesIndefJ_5d6a03c17248
-- name    : P2M_GroundTheory_Heights__Theta_conjTranspose_preservesIndefJ_5d6a03c17248
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:26.409632+00:00
-- url     : https://prove2.me/theorems/0d7c8c15-e1c3-5ab4-9688-237bc0bddd2f
-- title:
--   P2 M Ground Theory Heights  Theta conj Transpose preserves Indef J 5d6a03c17248: P2 M Ground Theory Heights  Theta conj Transpose preserves Indef J 5d6a03c17248
-- statement:
--   The P2 M Ground Theory Heights  Theta conj Transpose preserves Indef J 5d6a03c17248 construction uses the P2 M Ground Theory Heights  Theta conj Transpose preserves Indef J 5d6a03c17248 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean#L24-L26

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

theorem P2M_GroundTheory_Heights__Theta_conjTranspose_preservesIndefJ_5d6a03c17248 {g : 𝔐} (hg : gᴴ * J * g = J) : gᴴᴴ * J * gᴴ = J := by sorry

alias «GroundTheory».«Heights₂».«Theta».«conjTranspose_preservesIndefJ» := P2M_GroundTheory_Heights__Theta_conjTranspose_preservesIndefJ_5d6a03c17248
