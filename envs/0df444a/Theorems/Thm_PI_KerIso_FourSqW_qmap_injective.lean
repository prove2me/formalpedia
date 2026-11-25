-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_qmap_injective
-- name    : PI.KerIso.FourSqW.qmap_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:44.945712+00:00
-- url     : https://prove2.me/theorems/03a9b2d3-3050-55f5-8d35-8ce804d3cfab
-- title:
--   Four Sq W: qmap injective
-- statement:
--   The Four Sq W construction uses the qmap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean#L42-L58

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

theorem PI.KerIso.FourSqW.qmap_injective {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ) (hq : ∀ i, 0 < q i)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) :
    Function.Injective (qmap b Q) := by sorry
