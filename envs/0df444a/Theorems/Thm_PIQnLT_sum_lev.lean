-- Prove2me | Theorems.Thm_PIQnLT_sum_lev
-- name    : PIQnLT.sum_lev
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:07:54.759122+00:00
-- url     : https://prove2.me/theorems/a41b9ba3-7c81-423c-a455-fabbbce9d1cd
-- title:
--   PIQn LT: sum lev
-- statement:
--   The PIQn LT construction uses the sum lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L64-L76

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants
variable {k i r' : ℕ}

theorem PIQnLT.sum_lev {M : Type*} [AddCommMonoid M] (f : Fin (2 * (i + r') + k + 1) → M)
    (h : ∀ p : Fin (2 * (i + r') + k + 1), ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) → f p = 0) :
    ∑ p, f p = ∑ j : Fin (2 * r' + k + 1), f (levPos k i r' j) := by sorry
