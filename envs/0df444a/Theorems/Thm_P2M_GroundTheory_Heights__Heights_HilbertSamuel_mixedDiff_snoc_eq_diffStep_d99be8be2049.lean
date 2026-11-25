-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_snoc_eq_diffStep_d99be8be2049
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_snoc_eq_diffStep_d99be8be2049
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:47.666081+00:00
-- url     : https://prove2.me/theorems/0494f265-bf3c-5757-9cdb-4d8cd411dfaa
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff snoc eq diff Step d99be8be2049: P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff snoc eq diff Step d99be8be2049
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff snoc eq diff Step d99be8be2049 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff snoc eq diff Step d99be8be2049 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L20-L24

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_snoc_eq_diffStep_d99be8be2049 {n : ℕ} (bs : Fin n → K → ℤ) (b : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc bs b : Fin (n + 1) → K → ℤ) f = mixedDiff bs (diffStep b f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«mixedDiff_snoc_eq_diffStep» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_snoc_eq_diffStep_d99be8be2049
