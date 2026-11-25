-- Prove2me | Theorems.Thm_PI_LatMinWork_bound_span
-- name    : PI.LatMinWork.bound_span
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:44.384074+00:00
-- url     : https://prove2.me/theorems/54111c96-c74d-5faa-a897-2a6621ed815f
-- title:
--   Lat Min Work: bound span
-- statement:
--   The Lat Min Work construction uses the bound span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean#L27-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean#L27-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LatMinWork
variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]

theorem PI.LatMinWork.bound_span (B : V → V → ℚ_[p])
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (S : Set V) (w : V) (M : ℝ) (hM : 0 ≤ M) (hS : ∀ b ∈ S, ‖B b w‖ ≤ M) :
    ∀ v ∈ Submodule.span ℤ_[p] S, ‖B v w‖ ≤ M := by sorry
