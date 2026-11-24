-- Prove2me | Theorems.Thm_PIQnLT_hpk_out_in
-- name    : PIQnLT.hpk_out_in
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:07:55.796114+00:00
-- url     : https://prove2.me/theorems/4426ef40-6348-4343-b068-97148c61b66c
-- title:
--   PIQn LT: hpk out in
-- statement:
--   The PIQn LT construction uses the hpk out in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L100-L104

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

theorem PIQnLT.hpk_out_in (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) (hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) :
    Hpk k (i + r') p q = 0 := by sorry
