-- Prove2me | Theorems.Thm_P2M_PIQnLT__Lev_lev_250764e1f733
-- name    : P2M_PIQnLT__Lev_lev_250764e1f733
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:56:17.112426+00:00
-- url     : https://prove2.me/theorems/e33a9bb2-bf01-42a0-b671-27e375f3741b
-- title:
--   P2 M PIQn LT  Lev lev 250764e1f733: P2 M PIQn LT  Lev lev 250764e1f733
-- statement:
--   The P2 M PIQn LT  Lev lev 250764e1f733 construction uses the P2 M PIQn LT  Lev lev 250764e1f733 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L39-L51

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

theorem P2M_PIQnLT__Lev_lev_250764e1f733 (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g (levPos k i r' p) (levPos k i r' q) = g p q := by sorry

alias «PIQnLT».«ιLev_lev» := P2M_PIQnLT__Lev_lev_250764e1f733
