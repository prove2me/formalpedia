-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_succ_growth_natPow_86a645ae5dec
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_succ_growth_natPow_86a645ae5dec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:50.045784+00:00
-- url     : https://prove2.me/theorems/b3d3bc70-28ad-4295-bfcd-3e3af7abc1ee
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT succ growth nat Pow 86a645ae5dec: P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT succ growth nat Pow 86a645ae5dec
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT succ growth nat Pow 86a645ae5dec construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel deg LT succ growth nat Pow 86a645ae5dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L99-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L99-L182

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_succ_growth_natPow_86a645ae5dec (n : ℕ) : ∀ g : (K → ℤ) → ℤ, DegLT g (n + 1) →
    ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, A ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * (((∑ k, a k : ℕ) : ℝ) + 1) ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«degLT_succ_growth_natPow» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_succ_growth_natPow_86a645ae5dec
