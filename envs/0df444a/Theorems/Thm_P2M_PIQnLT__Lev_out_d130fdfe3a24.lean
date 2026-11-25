-- Prove2me | Theorems.Thm_P2M_PIQnLT__Lev_out_d130fdfe3a24
-- name    : P2M_PIQnLT__Lev_out_d130fdfe3a24
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:21.816934+00:00
-- url     : https://prove2.me/theorems/2296af55-a7fb-442b-affe-7487c41d8265
-- title:
--   P2 M PIQn LT  Lev out d130fdfe3a24: P2 M PIQn LT  Lev out d130fdfe3a24
-- statement:
--   The P2 M PIQn LT  Lev out d130fdfe3a24 construction uses the P2 M PIQn LT  Lev out d130fdfe3a24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean#L53-L56

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

theorem P2M_PIQnLT__Lev_out_d130fdfe3a24 (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = if p = q then 1 else 0 := by sorry

alias «PIQnLT».«ιLev_out» := P2M_PIQnLT__Lev_out_d130fdfe3a24
