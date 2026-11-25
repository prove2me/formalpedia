-- Prove2me | Theorems.Thm_PI_QnZeroLevelWork_quad_sum
-- name    : PI.QnZeroLevelWork.quad_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:49.518022+00:00
-- url     : https://prove2.me/theorems/51c18f48-3d7f-5d86-9452-90921199d301
-- title:
--   Qn Zero Level Work: quad sum
-- statement:
--   The Qn Zero Level Work construction uses the quad sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L52-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L52-L73

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem PI.QnZeroLevelWork.quad_sum {M : Type*} [AddCommMonoid M] {n : ℕ}
    (T : Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → M) :
    (∑ i : Fin (n + 2), ∑ i' : Fin (n + 2), ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
    ∑ i : Fin (n + 2), ∑ i'' : Fin (n + 1), ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0 := by sorry
