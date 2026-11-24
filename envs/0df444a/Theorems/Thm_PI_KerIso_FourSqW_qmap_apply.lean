-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_qmap_apply
-- name    : PI.KerIso.FourSqW.qmap_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:41.132611+00:00
-- url     : https://prove2.me/theorems/3e132459-cae2-4183-a8ef-d2681ea75c28
-- title:
--   Four Sq W: qmap apply
-- statement:
--   The Four Sq W construction uses the qmap apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean#L24-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerIso PI.KerIso.FourSqW
open PI.KerFourSqW

theorem PI.KerIso.FourSqW.qmap_apply {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → E) (w : Fin 4 × n) :
    qmap b Q x w = ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2 := by sorry
