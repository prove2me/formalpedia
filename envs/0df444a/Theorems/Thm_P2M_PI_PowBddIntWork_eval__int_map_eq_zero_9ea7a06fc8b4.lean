-- Prove2me | Theorems.Thm_P2M_PI_PowBddIntWork_eval__int_map_eq_zero_9ea7a06fc8b4
-- name    : P2M_PI_PowBddIntWork_eval__int_map_eq_zero_9ea7a06fc8b4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:06.640529+00:00
-- url     : https://prove2.me/theorems/80b69dc3-eec4-442e-b903-6d82fe302de1
-- title:
--   P2 M PI Pow Bdd Int Work eval  int map eq zero 9ea7a06fc8b4: P2 M PI Pow Bdd Int Work eval  int map eq zero 9ea7a06fc8b4
-- statement:
--   The P2 M PI Pow Bdd Int Work eval  int map eq zero 9ea7a06fc8b4 construction uses the P2 M PI Pow Bdd Int Work eval  int map eq zero 9ea7a06fc8b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerBoundedIntegrality/EvalIntMapEqZero.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerBoundedIntegrality/EvalIntMapEqZero.lean#L8-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_EvalIntMapEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PowBddIntWork
open Matrix Polynomial

theorem P2M_PI_PowBddIntWork_eval__int_map_eq_zero_9ea7a06fc8b4 {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (p : ℤ[X]) (a : A)
    (h : p.eval₂ (algebraMap ℤ A) a = 0) : p.eval₂ (algebraMap ℤ B) (ψ a) = 0 := by sorry

alias «PI».«PowBddIntWork».«eval₂_int_map_eq_zero» := P2M_PI_PowBddIntWork_eval__int_map_eq_zero_9ea7a06fc8b4
