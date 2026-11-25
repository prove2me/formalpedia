-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_lineFlag_isProper_c56852137958
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_lineFlag_isProper_c56852137958
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:12.796187+00:00
-- url     : https://prove2.me/theorems/068749e1-7a19-4e81-b227-f3674ffad628
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL line Flag is Proper c56852137958: P2 M Ground Theory Heights  Theta Fin GL line Flag is Proper c56852137958
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL line Flag is Proper c56852137958 construction uses the P2 M Ground Theory Heights  Theta Fin GL line Flag is Proper c56852137958 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L262-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L262-L271

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

theorem P2M_GroundTheory_Heights__Theta_FinGL_lineFlag_isProper_c56852137958 (hn : 1 < n) : (lineFlag n F hn).IsProper := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«lineFlag_isProper» := P2M_GroundTheory_Heights__Theta_FinGL_lineFlag_isProper_c56852137958
