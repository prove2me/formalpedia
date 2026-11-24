-- Prove2me | Theorems.Thm_PIQnLT_exp_Lz
-- name    : PIQnLT.exp_Lz
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:28:24.88979+00:00
-- url     : https://prove2.me/theorems/36fbefd6-fa01-4a33-ae7c-9a08fcecafb7
-- title:
--   PIQn LT: exp Lz
-- statement:
--   The PIQn LT construction uses the exp Lz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/ExpLz.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/ExpLz.lean#L17-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem PIQnLT.exp_Lz (hL : LevHom) (Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    NormedSpace.exp (Lz k i r' Y) = ιLev k i r' (NormedSpace.exp Y) := by sorry
