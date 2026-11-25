-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_entire_polynomialGrowth_one_var_410c9b15615f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_entire_polynomialGrowth_one_var_410c9b15615f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:30.103446+00:00
-- url     : https://prove2.me/theorems/ef33863c-7f06-5816-9e4c-4cbcd3249640
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel entire polynomial Growth one var 410c9b15615f: P2 M Ground Theory Heights  Heights Hilbert Samuel entire polynomial Growth one var 410c9b15615f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel entire polynomial Growth one var 410c9b15615f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel entire polynomial Growth one var 410c9b15615f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PEntirePolynomialGrowth.lean#L9-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PEntirePolynomialGrowth.lean#L9-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PEntirePolynomialGrowth
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
open MvPolynomial Metric

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_entire_polynomialGrowth_one_var_410c9b15615f (M : ℕ) : ∀ (g : ℂ → ℂ) (C : ℝ), Differentiable ℂ g →
    (∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ M) →
    ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧ ∀ z, g z = q.eval z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«entire_polynomialGrowth_one_var» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_entire_polynomialGrowth_one_var_410c9b15615f
