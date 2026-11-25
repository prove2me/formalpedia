-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_isIrreducible_trivial_9a2bb254c85d
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_isIrreducible_trivial_9a2bb254c85d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:39.252314+00:00
-- url     : https://prove2.me/theorems/4fee1dc6-e139-4cc8-87c0-b6820ee2947d
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL is Irreducible trivial 9a2bb254c85d: P2 M Ground Theory Heights  Theta Fin GL is Irreducible trivial 9a2bb254c85d
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL is Irreducible trivial 9a2bb254c85d construction uses the P2 M Ground Theory Heights  Theta Fin GL is Irreducible trivial 9a2bb254c85d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L289-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L289-L297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FinGL
open Matrix
noncomputable section
variable {n : ℕ} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Theta_FinGL_isIrreducible_trivial_9a2bb254c85d (G : Type*) [Group G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«isIrreducible_trivial» := P2M_GroundTheory_Heights__Theta_FinGL_isIrreducible_trivial_9a2bb254c85d
