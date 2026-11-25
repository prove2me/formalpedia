-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_ana_pi
-- name    : PI.SqfPrimeFactor.W.ana_pi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:22.682863+00:00
-- url     : https://prove2.me/theorems/126cc49a-1b73-45f6-b49e-10469e8022de
-- title:
--   W: ana pi
-- statement:
--   The W construction uses the ana pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/AnaCore.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/AnaCore.lean#L51-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset

theorem PI.SqfPrimeFactor.W.ana_pi (r : ℕ) (hr : 100 ≤ r) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    Nat.primeCounting r ≤ Nat.primeCounting (r / 2) + S.card + 2 := by sorry
