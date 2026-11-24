-- Prove2me | Theorems.Thm_P2M_PIQnLT__Lev_eq_d6fc93f29a45
-- name    : P2M_PIQnLT__Lev_eq_d6fc93f29a45
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:25.967404+00:00
-- url     : https://prove2.me/theorems/5041739f-72ef-4cf6-be49-c00a021a7f06
-- title:
--   P2 M PIQn LT  Lev eq d6fc93f29a45: P2 M PIQn LT  Lev eq d6fc93f29a45
-- statement:
--   The P2 M PIQn LT  Lev eq d6fc93f29a45 construction uses the P2 M PIQn LT  Lev eq d6fc93f29a45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L112-L116

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

theorem P2M_PIQnLT__Lev_eq_d6fc93f29a45 (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' X = Lz k i r' X + ιLev k i r' 0 := by sorry

alias «PIQnLT».«ιLev_eq» := P2M_PIQnLT__Lev_eq_d6fc93f29a45
