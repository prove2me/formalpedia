-- Prove2me | Theorems.Thm_PI_LatMinWork_main
-- name    : PI.LatMinWork.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:34:09.359567+00:00
-- url     : https://prove2.me/theorems/4c015ac1-fcaf-4677-b005-91f177a2d23c
-- title:
--   Lat Min Work: main
-- statement:
--   The Lat Min Work construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean#L50-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean#L50-L110

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

theorem PI.LatMinWork.main (hp2 : p ≠ 2) (B : V → V → ℚ_[p]) (L : Submodule ℤ_[p] V) (hL : L.FG)
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (hsym : ∀ u ∈ L, ∀ v ∈ L, B u v = B v u) (hne : ∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) :
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x := by sorry
