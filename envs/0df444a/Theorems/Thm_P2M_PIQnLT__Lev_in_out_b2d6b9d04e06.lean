-- Prove2me | Theorems.Thm_P2M_PIQnLT__Lev_in_out_b2d6b9d04e06
-- name    : P2M_PIQnLT__Lev_in_out_b2d6b9d04e06
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:17.802868+00:00
-- url     : https://prove2.me/theorems/305be2a2-2833-5666-8c4b-bc633d22bb4d
-- title:
--   P2 M PIQn LT  Lev in out b2d6b9d04e06: P2 M PIQn LT  Lev in out b2d6b9d04e06
-- statement:
--   The P2 M PIQn LT  Lev in out b2d6b9d04e06 construction uses the P2 M PIQn LT  Lev in out b2d6b9d04e06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L58-L62

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

theorem P2M_PIQnLT__Lev_in_out_b2d6b9d04e06 (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = 0 := by sorry

alias «PIQnLT».«ιLev_in_out» := P2M_PIQnLT__Lev_in_out_b2d6b9d04e06
