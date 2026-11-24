-- Prove2me | Theorems.Thm_PIQnLT_lev_inj
-- name    : PIQnLT.lev_inj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:25.338149+00:00
-- url     : https://prove2.me/theorems/ba0fb4ca-80af-4150-8e98-d23343352be5
-- title:
--   PIQn LT: lev inj
-- statement:
--   The PIQn LT construction uses the lev inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L16-L21

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

theorem PIQnLT.lev_inj : Function.Injective (levPos k i r') := by sorry
