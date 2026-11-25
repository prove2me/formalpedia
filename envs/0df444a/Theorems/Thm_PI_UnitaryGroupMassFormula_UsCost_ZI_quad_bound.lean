-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_quad_bound
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.quad_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:32.334445+00:00
-- url     : https://prove2.me/theorems/5b898993-db0a-47ba-8b33-15e856d4ffea
-- title:
--   ZI: quad bound
-- statement:
--   The ZI construction uses the quad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean#L57-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.quad_bound (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ∀ a ≤ n, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by sorry
