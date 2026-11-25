-- Prove2me | Theorems.Thm_PI_WA_g_small_pow_mul
-- name    : PI.WA.g_small_pow_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:44:01.94406+00:00
-- url     : https://prove2.me/theorems/1816c2b6-8bea-42c8-8274-6c0b585e7c43
-- title:
--   WA: g small pow mul
-- statement:
--   The WA construction uses the g small pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExistenceHolds.lean#L21-L23

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

theorem PI.WA.g_small_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y)
    (r : ℕ) (hr : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * Y) := by sorry
