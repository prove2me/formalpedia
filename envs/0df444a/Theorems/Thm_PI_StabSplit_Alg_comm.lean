-- Prove2me | Theorems.Thm_PI_StabSplit_Alg_comm
-- name    : PI.StabSplit.Alg.comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:24.739061+00:00
-- url     : https://prove2.me/theorems/5ae70886-c795-43b7-a7e3-24f4bec8a6c0
-- title:
--   Alg: comm
-- statement:
--   The Alg construction uses the comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/UnitR.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/UnitR.lean#L37-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.StabSplit PI.StabSplit.Alg
variable {R : Type*} [Ring R]

theorem PI.StabSplit.Alg.comm (P ρ κ : R) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hρM : (1 - P) * ρ * P = 0) (hκU : P * κ * (1 - P) = 0) : ρ * κ = κ * ρ := by sorry
