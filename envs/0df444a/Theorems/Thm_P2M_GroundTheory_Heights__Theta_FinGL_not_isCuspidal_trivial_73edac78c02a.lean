-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_not_isCuspidal_trivial_73edac78c02a
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_not_isCuspidal_trivial_73edac78c02a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:13.530615+00:00
-- url     : https://prove2.me/theorems/d4847380-fd69-5449-97ac-6cfc52818a8a
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL not is Cuspidal trivial 73edac78c02a: P2 M Ground Theory Heights  Theta Fin GL not is Cuspidal trivial 73edac78c02a
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL not is Cuspidal trivial 73edac78c02a construction uses the P2 M Ground Theory Heights  Theta Fin GL not is Cuspidal trivial 73edac78c02a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L273-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L273-L276

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

theorem P2M_GroundTheory_Heights__Theta_FinGL_not_isCuspidal_trivial_73edac78c02a (hn : 1 < n) :
    ¬ IsCuspidal n F (Representation.trivial ℂ (GL (Fin n) F) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«not_isCuspidal_trivial» := P2M_GroundTheory_Heights__Theta_FinGL_not_isCuspidal_trivial_73edac78c02a
