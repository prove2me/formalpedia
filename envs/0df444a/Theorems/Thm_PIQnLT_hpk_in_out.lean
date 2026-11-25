-- Prove2me | Theorems.Thm_PIQnLT_hpk_in_out
-- name    : PIQnLT.hpk_in_out
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:02.477898+00:00
-- url     : https://prove2.me/theorems/8406e2ac-3441-4b5c-ad8c-7f160e634291
-- title:
--   PIQn LT: hpk in out
-- statement:
--   The PIQn LT construction uses the hpk in out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L94-L98

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

theorem PIQnLT.hpk_in_out (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    Hpk k (i + r') p q = 0 := by sorry
