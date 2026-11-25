-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_qmap_back
-- name    : PI.KerIso.FourSqW.qmap_back
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:02.825068+00:00
-- url     : https://prove2.me/theorems/eca4b013-761e-4a8c-b032-411a2a6e5423
-- title:
--   Four Sq W: qmap back
-- statement:
--   The Four Sq W construction uses the qmap back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean#L28-L40

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

theorem PI.KerIso.FourSqW.qmap_back {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x : Fin 4 → E) (a' : Fin 4) (i : n) :
    ∑ c, (Q i c a' : K) * qmap b Q x (c, i) = (q i : K) * b.repr (x a') i := by sorry
