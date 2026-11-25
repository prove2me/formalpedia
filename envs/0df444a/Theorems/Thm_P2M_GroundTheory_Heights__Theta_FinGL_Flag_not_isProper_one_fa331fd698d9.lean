-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_Flag_not_isProper_one_fa331fd698d9
-- name    : P2M_GroundTheory_Heights__Theta_FinGL_Flag_not_isProper_one_fa331fd698d9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:16.153387+00:00
-- url     : https://prove2.me/theorems/e846bb82-7640-4df0-9e9e-98ffffd3ea4f
-- title:
--   P2 M Ground Theory Heights  Theta Fin GL Flag not is Proper one fa331fd698d9: P2 M Ground Theory Heights  Theta Fin GL Flag not is Proper one fa331fd698d9
-- statement:
--   The P2 M Ground Theory Heights  Theta Fin GL Flag not is Proper one fa331fd698d9 construction uses the P2 M Ground Theory Heights  Theta Fin GL Flag not is Proper one fa331fd698d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L278-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean#L278-L283

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

theorem P2M_GroundTheory_Heights__Theta_FinGL_Flag_not_isProper_one_fa331fd698d9 (𝓕 : Flag 1 F) : ¬ 𝓕.IsProper := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FinGL».«Flag».«not_isProper_one» := P2M_GroundTheory_Heights__Theta_FinGL_Flag_not_isProper_one_fa331fd698d9
