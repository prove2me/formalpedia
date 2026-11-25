-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_of_degLT_succ_1dbb35a03f6d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_of_degLT_succ_1dbb35a03f6d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:05.376812+00:00
-- url     : https://prove2.me/theorems/d549d914-cdb7-4d97-a7dd-83eeb721f7ff
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step of deg LT succ 1dbb35a03f6d: P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step of deg LT succ 1dbb35a03f6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step of deg LT succ 1dbb35a03f6d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT diff Step of deg LT succ 1dbb35a03f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L28-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_of_degLT_succ_1dbb35a03f6d {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1)) (b : K → ℤ) :
    DegLT (diffStep b f) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«degLT_diffStep_of_degLT_succ» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_of_degLT_succ_1dbb35a03f6d
