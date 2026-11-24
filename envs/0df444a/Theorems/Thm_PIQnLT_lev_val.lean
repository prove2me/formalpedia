-- Prove2me | Theorems.Thm_PIQnLT_lev_val
-- name    : PIQnLT.lev_val
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:07:43.272033+00:00
-- url     : https://prove2.me/theorems/2b074e1d-763a-49cf-942f-33e37d9f3eea
-- title:
--   PIQn LT: lev val
-- statement:
--   The PIQn LT construction uses the lev val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L14-L14

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

theorem PIQnLT.lev_val (j : Fin (2 * r' + k + 1)) : (levPos k i r' j).val = j.val + i := by sorry
