-- Prove2me | Theorems.Thm_PIQnLT_Lz_mul
-- name    : PIQnLT.Lz_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:27.167216+00:00
-- url     : https://prove2.me/theorems/aa28f5f9-9d8d-414b-a4af-b9c65ba7e084
-- title:
--   PIQn LT: Lz mul
-- statement:
--   The PIQn LT construction uses the Lz mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L158-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L158-L174

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

theorem PIQnLT.Lz_mul (X Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (X * Y) = Lz k i r' X * Lz k i r' Y := by sorry
