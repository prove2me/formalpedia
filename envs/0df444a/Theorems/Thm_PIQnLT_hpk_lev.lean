-- Prove2me | Theorems.Thm_PIQnLT_hpk_lev
-- name    : PIQnLT.hpk_lev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:07:57.569155+00:00
-- url     : https://prove2.me/theorems/0d6c30e0-d400-484b-ab8a-b92e7404b82a
-- title:
--   PIQn LT: hpk lev
-- statement:
--   The PIQn LT construction uses the hpk lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L78-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L78-L92

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

theorem PIQnLT.hpk_lev (p q : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' p) (levPos k i r' q) = Hpk k r' p q := by sorry
