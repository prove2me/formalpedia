-- Prove2me | Theorems.Thm_PI_WA_g_int_pow_mul
-- name    : PI.WA.g_int_pow_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:44:08.790509+00:00
-- url     : https://prove2.me/theorems/3ccab7b4-b955-43e4-8a4b-32dae61032bf
-- title:
--   WA: g int pow mul
-- statement:
--   The WA construction uses the g int pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean#L25-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WA
open PI.WADVR
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}

theorem PI.WA.g_int_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 0 q) (hY : Sm Q ϖ 1 Y) (r : ℕ) :
    Sm Q ϖ 1 (q ^ r * Y) := by sorry
