-- Prove2me | Theorems.Thm_PIQnLT_Lz_pow
-- name    : PIQnLT.Lz_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:03.54849+00:00
-- url     : https://prove2.me/theorems/747242cf-bede-40d6-a430-cadafc60a24c
-- title:
--   PIQn LT: Lz pow
-- statement:
--   The PIQn LT construction uses the Lz pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L180-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L180-L184

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
variable (hL : LevHom)
include hL

theorem PIQnLT.Lz_pow (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (n : ℕ) :
    Lz k i r' (X ^ (n + 1)) = Lz k i r' X ^ (n + 1) := by sorry
